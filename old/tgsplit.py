#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
tgsplit — независимые TAR-архивы до заданного размера для Telegram.

Формат 2: NAME.0001.tar, NAME.0002.tar, …; рядом NAME.plan.json — главный
файл состояния (его нельзя удалять). Каждый архив самодостаточен, без сжатия;
первый член — .tgsplit/manifest.json, последний — .tgsplit/entries.sha256.
Большие файлы режутся на NAME.tgsfrag0001, …; остальные файлы не режутся.
Полные фрагменты имеют длину, кратную 512; последний остаток хранит точное
число байт исходного файла. Фрагменты можно вручную соединить через cat или
copy /b в порядке номеров.

Сохраняются относительные пути, режимы, mtime с точностью до секунды,
символические ссылки и пустые папки. Жёсткие ссылки сохраняются как отдельные
файлы. ACL, xattr, атрибуты Windows, uid/gid и жёсткие связи не сохраняются.
Источники не должны меняться: перед архивом и после него проверяются размер
и mtime_ns. Обычное продолжение игнорирует новые файлы. Команда extend добавляет
их в новые архивы, а перенесённые файлы распознаёт по сохранённому SHA256,
не пересоздавая старые архивы и сохраняя исходный plan_id.

Консоль:
    python tgsplit.py plan ПУТЬ... -o OUT [-s 1900M]
    python tgsplit.py split ПУТЬ... -o OUT [-s 1900M] [--max-parts N]
    python tgsplit.py split -o OUT [--max-parts N]
    python tgsplit.py extend -o OUT [--max-parts N] [--plan-only] [--add НОВАЯ_ПАПКА]
    python tgsplit.py status OUT
    python tgsplit.py verify OUT
    python tgsplit.py join АРХИВ_ИЛИ_ПАПКА... [-o OUT]

Команда plan — сухой запуск: архивы не создаются, но план сохраняется атомарно.
При повторном планировании после потери plan.json статусы существующих архивов
восстанавливаются из их манифестов. Удалённые архивы будут созданы заново.
Без аргументов открывается графическое окно. Старый потоковый формат
name.tar.001, name.tar.002, … по-прежнему поддерживается командой join.

Только стандартная библиотека, Python 3.8+. Для перетаскивания в GUI можно
отдельно установить tkinterdnd2; без него GUI и консоль работают полностью.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import io
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
from pathlib import Path, PurePosixPath

MiB = 1024 ** 2
DEFAULT_PART_MB = 1900
DEFAULT_PART_SIZE = DEFAULT_PART_MB * MiB
MIN_PART_SIZE = 64 * 1024
CHUNK = 4 * MiB
HASH_LOG_THRESHOLD = 64 * MiB
BLOCK = 512
RECORD = 10240
FORMAT_VERSION = 2
RESTORE_STATE = ".tgsplit-restore.json"
PART_RE = re.compile(r"^(?P<base>.+)\.(?P<num>\d{3,})$")
ARCHIVE_RE = re.compile(r"^(?P<base>.+)\.(?P<num>\d{4})\.tar$")


class Cancelled(Exception):
    pass


class IntegrityError(Exception):
    pass


def human(n):
    n = float(n)
    for unit in ("Б", "КБ", "МБ", "ГБ", "ТБ"):
        if n < 1024 or unit == "ТБ":
            return "{:.0f} {}".format(n, unit) if unit == "Б" else "{:.1f} {}".format(n, unit)
        n /= 1024
    return "{:.1f} ТБ".format(n)


def parse_size(text):
    m = re.fullmatch(r"\s*(\d+(?:[.,]\d+)?)\s*([KkMmGg]?)[Bb]?\s*", str(text))
    if not m:
        raise ValueError("Не понимаю размер «{}». Примеры: 1900, 1900M, 1.8G".format(text))
    mult = {"": MiB, "K": 1024, "M": MiB, "G": 1024 ** 3}[m.group(2).upper()]
    size = int(float(m.group(1).replace(",", ".")) * mult)
    if size < MIN_PART_SIZE:
        raise ValueError("Размер части должен быть не меньше {}".format(human(MIN_PART_SIZE)))
    return size


def round_up(n, unit=BLOCK):
    return ((n + unit - 1) // unit) * unit


def canonical_json(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")


def atomic_json(path, value):
    path = Path(path)
    fd, tmp = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(fd, "wb") as f:
            data = canonical_json(value) + b"\n"
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, str(path))
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def _is_inside(child, parent):
    try:
        Path(os.path.realpath(str(child))).relative_to(os.path.realpath(str(parent)))
        return True
    except ValueError:
        return False


def needs_pax(text, limit=99):
    return len(text.encode("utf-8", "surrogateescape")) > limit or not text.isascii()


def pax_cost(text, limit=99, keyword="path"):
    if not needs_pax(text, limit):
        return 0
    raw = text.encode("utf-8", "surrogateescape")
    length = len(raw) + len(keyword) + 12
    while True:
        n = len(str(length)) + len(keyword) + 3 + len(raw) + 1
        if n == length:
            return BLOCK + round_up(n)
        length = n


def stored_entry_cost(entry):
    name = entry["path"]
    cost = BLOCK + pax_cost(name)
    if entry["type"] == "symlink":
        cost += pax_cost(entry.get("linkname", ""), 100, "linkpath")
    if entry["type"] == "file":
        cost += round_up(entry["size"])
    return cost


def fragment_name(path, index):
    return "{}.tgsfrag{:04d}".format(path, index)


def manifest_for_archive(plan, archive, total_count=None):
    manifest = {
        "format": FORMAT_VERSION,
        "plan_id": plan["plan_id"],
        "archive": archive["index"],
        "total_archives": archive.get("total_archives", 0) if total_count is None else total_count,
        "entries": archive["entries"],
    }
    if archive.get("operations"):
        manifest["operations"] = archive["operations"]
    if archive.get("omitted"):
        manifest["omitted"] = archive["omitted"]
    return manifest


def metadata_cost(plan, archive):
    manifest = canonical_json(manifest_for_archive(plan, archive, 0))
    entries_size = sum(68 + len(e["path"].encode("utf-8", "surrogateescape")) for e in archive["entries"])
    return (BLOCK + round_up(len(manifest) + 1024) +
            BLOCK + round_up(entries_size + 128) + round_up(1024, RECORD))


def archive_estimate(plan, archive):
    return metadata_cost(plan, archive) + sum(stored_entry_cost(e) for e in archive["entries"])


def _new_archive(index):
    return {"index": index, "status": "pending", "entries": [], "sha256": None, "size": 0}


def _finish_archive(plan, archive, part_size):
    archive["size"] = archive_estimate(plan, archive)
    if archive["size"] > part_size:
        raise ValueError("Внутренняя ошибка планировщика: оценка больше размера части")
    return archive


def _fits(plan, archive, entry, part_size):
    candidate = dict(archive)
    candidate["entries"] = archive["entries"] + [entry]
    return archive_estimate(plan, candidate) <= part_size


def _max_fragment(plan, logical, part_size):
    base = {
        "path": fragment_name(logical["path"], 1), "source_path": logical["path"],
        "type": "file", "size": 0, "mode": logical["mode"], "mtime": logical["mtime"],
        "fragment": {"index": 1, "count": 1, "offset": 0, "length": 0,
                     "total_size": logical["size"]},
    }
    archive = _new_archive(1)
    archive["entries"] = [base]
    fixed = metadata_cost(plan, archive) + BLOCK + pax_cost(base["path"])
    high = max(0, (part_size - fixed) // BLOCK)
    low = 0
    while low < high:
        mid = (low + high + 1) // 2
        base["size"] = mid * BLOCK
        base["fragment"]["length"] = mid * BLOCK
        archive["size"] = 0
        if archive_estimate(plan, archive) <= part_size:
            low = mid
        else:
            high = mid - 1
    if low == 0:
        raise ValueError("Размер части слишком мал даже для одного фрагмента: {}".format(logical["path"]))
    return low * BLOCK


def _fragment(logical, index, count, offset, length):
    return {
        "path": fragment_name(logical["path"], index), "source_path": logical["path"],
        "type": "file", "size": length, "mode": logical["mode"], "mtime": logical["mtime"],
        "fragment": {"index": index, "count": count, "offset": offset, "length": length,
                     "total_size": logical["size"]},
    }


def _stored_whole(logical):
    keys = ("path", "type", "size", "mode", "mtime")
    result = {k: logical[k] for k in keys}
    if logical["type"] == "symlink":
        result["linkname"] = logical["linkname"]
    return result


def pack_entries(plan, part_size):
    archives = []
    current = None
    for logical in plan["files"]:
        whole = _stored_whole(logical)
        if current is not None and _fits(plan, current, whole, part_size):
            current["entries"].append(whole)
            continue
        empty = _new_archive(current["index"] + 1 if current is not None else len(archives) + 1)
        if _fits(plan, empty, whole, part_size):
            if current is not None:
                archives.append(_finish_archive(plan, current, part_size))
            empty["entries"].append(whole)
            current = empty
            continue
        if logical["type"] != "file":
            raise ValueError("Элемент не помещается в архив: {}".format(logical["path"]))
        if current is not None:
            archives.append(_finish_archive(plan, current, part_size))
            current = None
        capacity = _max_fragment(plan, logical, part_size)
        count = (logical["size"] + capacity - 1) // capacity
        offset = 0
        for index in range(1, count + 1):
            length = min(capacity, logical["size"] - offset)
            frag = _fragment(logical, index, count, offset, length)
            archive = _new_archive(len(archives) + 1)
            archive["entries"].append(frag)
            _finish_archive(plan, archive, part_size)
            if index < count:
                archives.append(archive)
            else:
                current = archive
            offset += length
    if current is not None:
        archives.append(_finish_archive(plan, current, part_size))
    for archive in archives:
        archive["total_archives"] = len(archives)
    return archives


def _duplicate_name(name, used):
    if name not in used:
        used.add(name)
        return name
    p = PurePosixPath(name)
    suffix = "".join(p.suffixes)
    stem = name[:-len(suffix)] if suffix else name
    number = 2
    while True:
        candidate = "{}_{}{}".format(stem, number, suffix)
        if candidate not in used:
            used.add(candidate)
            return candidate
        number += 1


def _logical_from_stat(source, arcname, st):
    mode = stat.S_IMODE(st.st_mode)
    base = {"source": str(source), "path": arcname, "mode": mode,
            "mtime": int(st.st_mtime), "mtime_ns": st.st_mtime_ns}
    if stat.S_ISREG(st.st_mode):
        base.update(type="file", size=st.st_size)
    elif stat.S_ISDIR(st.st_mode):
        base.update(type="dir", size=0)
    elif stat.S_ISLNK(st.st_mode):
        base.update(type="symlink", size=0, linkname=os.readlink(str(source)))
    else:
        raise ValueError("неподдерживаемый тип файла")
    return base


def scan_sources(paths, log=print, progress=None, cancel=None):
    tops = [Path(os.path.abspath(str(p))) for p in paths]
    if not tops:
        raise ValueError("Не выбрано ни одного файла или папки")
    for p in tops:
        if not os.path.lexists(str(p)):
            raise ValueError("Не найдено: {}".format(p))
    real = [os.path.realpath(str(p)) for p in tops]
    for i, p in enumerate(real):
        for j in range(i):
            if _is_inside(p, real[j]) or _is_inside(real[j], p):
                raise ValueError("Вложенные источники недопустимы: {} и {}".format(tops[j], tops[i]))
    files = []
    skipped = []
    sources = []
    used = set()

    def walk(source, arcname):
        try:
            entries = sorted(os.scandir(str(source)), key=lambda e: e.name)
        except OSError as e:
            skipped.append({"path": str(source), "reason": "не удалось прочитать папку: {}".format(e)})
            log("Пропущено содержимое {}: {}".format(source, e))
            return
        for child in entries:
            child_path = Path(child.path)
            child_name = PurePosixPath(arcname) / child.name
            add(child_path, child_name.as_posix())

    def add(source, arcname):
        try:
            st = os.lstat(str(source))
            logical = _logical_from_stat(source, arcname, st)
            if logical["type"] == "file":
                size = logical["size"]
                if size >= HASH_LOG_THRESHOLD:
                    log("Хэширование: {} ({})".format(source, human(size)))
                file_progress = (lambda done, size=size: progress(done, size)) if progress else None
                logical["sha256"] = hash_file(source, file_progress, cancel)
        except (OSError, ValueError) as e:
            skipped.append({"path": str(source), "archive_path": arcname, "reason": str(e)})
            log("Пропущено {}: {}".format(source, e))
            return
        files.append(logical)
        if logical["type"] == "dir":
            walk(source, arcname)

    for top in tops:
        st = os.lstat(str(top))
        name = _duplicate_name(top.name or "archive", used)
        sources.append({"path": str(top), "name": name})
        add(top, name)
    return sources, files, skipped


def calculate_plan_id(sources, part_size, files):
    value = {
        "sources": sources,
        "part_size": part_size,
        "files": [{k: f[k] for k in ("path", "type", "size", "mtime_ns")} for f in files],
    }
    return hashlib.sha256(canonical_json(value)).hexdigest()


def make_plan(paths, out_dir, part_size=DEFAULT_PART_SIZE, name=None, log=print,
              progress=None, cancel=None):
    out = Path(os.path.abspath(str(out_dir)))
    sources, files, skipped = scan_sources(paths, log=log, progress=progress, cancel=cancel)
    if not name:
        name = sources[0]["name"] if len(sources) == 1 else "archive"
    name = Path(name).name
    if not name or name in (".", ".."):
        raise ValueError("Некорректное имя архива")
    for p in paths:
        if os.path.isdir(str(p)) and not os.path.islink(str(p)) and _is_inside(out, p):
            raise ValueError("Папка результата не должна лежать внутри упаковываемой папки")
    plan = {
        "format": FORMAT_VERSION, "name": name, "sources": sources,
        "parameters": {"part_size": part_size}, "files": files, "skipped": skipped,
    }
    plan["plan_id"] = calculate_plan_id(sources, part_size, files)
    plan["archives"] = pack_entries(plan, part_size)
    return plan


def plan_path(out, name=None):
    out = Path(out)
    if out.name.endswith(".plan.json"):
        return out
    if name:
        return out / "{}.plan.json".format(name)
    found = sorted(out.glob("*.plan.json")) if out.is_dir() else []
    if len(found) != 1:
        raise ValueError("Укажите имя плана: в OUT найдено {} файлов *.plan.json".format(len(found)))
    return found[0]


def load_plan(out, name=None):
    path = plan_path(out, name)
    with open(str(path), "r", encoding="utf-8") as f:
        plan = json.load(f)
    if plan.get("format") != FORMAT_VERSION:
        raise ValueError("Неподдерживаемая версия плана: {}".format(path))
    return plan


def print_plan(plan, log=print):
    log("План {}: {} архивов, {}".format(plan["name"], len(plan["archives"]), human(
        sum(f["size"] for f in plan["files"] if f["type"] == "file"))))
    for a in plan["archives"]:
        log("  {:04d}: {:3d} элементов, оценка {}, {}".format(
            a["index"], len(a["entries"]), human(a["size"]), a["status"]))
    if plan["skipped"]:
        log("Пропущено: {}".format(len(plan["skipped"])))


def recover_archives(plan, out_dir, log=print):
    out = Path(out_dir)
    for archive in plan["archives"]:
        path = archive_path(out, plan, archive["index"])
        if not path.is_file():
            continue
        try:
            with tarfile.open(str(path), "r:") as tar:
                member = tar.next()
                if member is None or member.name != ".tgsplit/manifest.json":
                    continue
                manifest = json.load(tar.extractfile(member))
            if manifest.get("plan_id") != plan["plan_id"] or manifest.get("entries") != archive["entries"]:
                continue
            digest = hashlib.sha256()
            with open(str(path), "rb") as f:
                while True:
                    data = f.read(CHUNK)
                    if not data:
                        break
                    digest.update(data)
            archive.update(status="done", sha256=digest.hexdigest(), size=path.stat().st_size)
            log("Восстановлен статус готового архива: {}".format(path.name))
        except (OSError, tarfile.TarError, ValueError, KeyError):
            continue


def create_plan(paths, out_dir, part_size=DEFAULT_PART_SIZE, name=None, log=print, recover=False,
                progress=None, cancel=None):
    out = Path(os.path.abspath(str(out_dir)))
    out.mkdir(parents=True, exist_ok=True)
    plan = make_plan(paths, out, part_size, name, log, progress, cancel)
    path = out / "{}.plan.json".format(plan["name"])
    if path.exists():
        raise ValueError("План уже существует: {}".format(path))
    if recover:
        recover_archives(plan, out, log)
    atomic_json(path, plan)
    return plan


def atomic_bytes(path, data):
    path = Path(path)
    fd, tmp = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, str(path))
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


@contextlib.contextmanager
def plan_lock(out_dir, name):
    lock = Path(out_dir) / "{}.lock".format(name)
    try:
        fd = os.open(str(lock), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        raise ValueError("Другой процесс уже работает с планом ({}). Если он завершился аварийно, удалите lock вручную.".format(lock))
    try:
        with os.fdopen(fd, "w", encoding="ascii") as f:
            f.write(str(os.getpid()))
        yield
    finally:
        try:
            lock.unlink()
        except OSError:
            pass


def parse_indices(text, total):
    result = []
    for word in text.split(","):
        try:
            value = int(word.strip())
        except ValueError:
            raise ValueError("Некорректный список архивов: {}".format(text))
        if value < 1 or value > total:
            raise ValueError("Архив {} вне диапазона 1..{}".format(value, total))
        if value not in result:
            result.append(value)
    if not result:
        raise ValueError("Пустой список архивов")
    return result


def check_possible_renames(plan, indices):
    """Не пропускать молча файлы, которые, вероятно, переименованы или перенесены, а не удалены."""
    files = source_map(plan)
    wanted = {}
    for index in indices:
        for logical_path in missing_sources(files, plan["archives"][index - 1]):
            size = files[logical_path]["size"]
            if size > 0:
                wanted.setdefault(size, []).append(logical_path)
    if not wanted:
        return
    planned = {f["source"] for f in plan["files"]}
    found = []
    for source in plan["sources"]:
        root = source["path"]
        if os.path.isdir(root) and not os.path.islink(root):
            walker = os.walk(root)
        else:
            walker = [(os.path.dirname(root), [], [os.path.basename(root)])]
        for current, dirs, names in walker:
            for name in names:
                path = os.path.join(current, name)
                if path in planned:
                    continue
                try:
                    st = os.lstat(path)
                except OSError:
                    continue
                if stat.S_ISREG(st.st_mode) and st.st_size in wanted:
                    found.append((wanted[st.st_size][0], path))
    if found:
        lines = ["  {} -> {}".format(old, new) for old, new in found[:5]]
        if len(found) > 5:
            lines.append("  … и ещё {}".format(len(found) - 5))
        raise ValueError(
            "Похоже, часть файлов переименована или перенесена: исходных файлов нет, "
            "а на диске есть новые файлы такого же размера:\n{}\n"
            "Сначала обновите план («Обновить план» / extend --plan-only), чтобы переносы были учтены, "
            "и повторите. Архивы не созданы.".format("\n".join(lines)))


def warn_new_files(plan, indices, log=print):
    selected = [plan["archives"][i - 1] for i in indices]
    logical_paths = {e.get("source_path", e["path"]) for a in selected for e in a["entries"]}
    planned = {f["source"] for f in plan["files"]}
    warned = set()
    for source in plan["sources"]:
        root = source["path"]
        prefix = source["name"] + "/"
        if not any(p == source["name"] or p.startswith(prefix) for p in logical_paths):
            continue
        if not os.path.isdir(root) or os.path.islink(root):
            continue
        for current, dirs, files in os.walk(root):
            for name in dirs + files:
                path = os.path.join(current, name)
                if path not in planned and path not in warned:
                    warned.add(path)
                    log("Новый источник проигнорирован (его нет в плане): {}".format(path))


def split_plan(paths, out_dir, part_size=DEFAULT_PART_SIZE, name=None, max_parts=None,
               only=None, redo=None, log=print, progress=None, cancel=None, hash_progress=None):
    out = Path(os.path.abspath(str(out_dir)))
    out.mkdir(parents=True, exist_ok=True)
    existing = None
    if name:
        candidate = out / "{}.plan.json".format(name)
        if candidate.exists():
            existing = candidate
    else:
        found = sorted(out.glob("*.plan.json"))
        if len(found) == 1:
            existing = found[0]
        elif len(found) > 1:
            raise ValueError("В OUT несколько планов; укажите -n")
    lock_name = name or (Path(existing).name[:-10] if existing else
                         (Path(paths[0]).name if len(paths) == 1 else "archive"))
    with plan_lock(out, lock_name):
        if existing:
            plan = load_plan(existing)
            if paths:
                given = [os.path.abspath(str(p)) for p in paths]
                if given != [s["path"] for s in plan["sources"]]:
                    raise ValueError("Переданные пути не совпадают с существующим планом")
            if name and name != plan["name"]:
                raise ValueError("Имя не совпадает с существующим планом")
        else:
            if not paths:
                raise ValueError("Для продолжения нужен существующий plan.json")
            log("Сканирование и вычисление SHA256 исходных файлов…")
            plan = create_plan(paths, out, part_size, name, log, recover=True,
                               progress=hash_progress, cancel=cancel)
        total = len(plan["archives"])
        if redo is not None:
            if only is not None or max_parts is not None:
                raise ValueError("--redo нельзя сочетать с --only или --max-parts")
            indices = parse_indices(redo, total)
            if any(plan["archives"][i - 1]["status"] != "done" for i in indices):
                raise ValueError("--redo предназначен только для готовых архивов")
        elif only is not None:
            if max_parts is not None:
                raise ValueError("--only нельзя сочетать с --max-parts")
            indices = parse_indices(only, total)
            if any(plan["archives"][i - 1]["status"] == "done" for i in indices):
                raise ValueError("Выбранный архив уже готов; используйте --redo")
        else:
            indices = [a["index"] for a in plan["archives"] if a["status"] == "pending"]
            if max_parts is not None:
                if max_parts < 1:
                    raise ValueError("--max-parts должен быть положительным")
                indices = indices[:max_parts]
        warn_new_files(plan, indices, log)
        check_possible_renames(plan, indices)
        try:
            for number, index in enumerate(indices, 1):
                old_hash = plan["archives"][index - 1].get("sha256")
                build_archive(plan, out, index, progress, cancel, log)
                new_hash = plan["archives"][index - 1]["sha256"]
                if redo is not None and old_hash and old_hash != new_hash:
                    log("ВНИМАНИЕ: sha256 пересозданного архива отличается: {} -> {}".format(old_hash, new_hash))
                log("Создано в этом запуске: {} из {}".format(number, len(indices)))
        except (Cancelled, KeyboardInterrupt):
            done_now = sum(a["status"] == "done" for a in plan["archives"])
            log("Отменено: готово {} из {}, запустите split снова для продолжения".format(done_now, total))
            raise Cancelled()
        log("Готово {} из {} архивов".format(sum(a["status"] == "done" for a in plan["archives"]), total))
        return plan


def save_plan_only(paths, out_dir, part_size=DEFAULT_PART_SIZE, name=None, log=print,
                   progress=None, cancel=None):
    """Построить и сохранить NAME.plan.json без создания архивов."""
    out = Path(os.path.abspath(str(out_dir)))
    out.mkdir(parents=True, exist_ok=True)
    if name and (out / "{}.plan.json".format(name)).exists() or (not name and list(out.glob("*.plan.json"))):
        raise ValueError("В папке результата уже есть план; используйте «Продолжить»")
    lock_name = name or (Path(paths[0]).name if len(paths) == 1 else "archive")
    with plan_lock(out, lock_name):
        log("Сканирование и вычисление SHA256 исходных файлов…")
        plan = create_plan(paths, out, part_size, name, log, recover=True,
                           progress=progress, cancel=cancel)
        log("План сохранён: {}".format(out / "{}.plan.json".format(plan["name"])))
        print_plan(plan, log)
        return plan


def print_status(plan, log=print):
    done = [a for a in plan["archives"] if a["status"] == "done"]
    pending = [a for a in plan["archives"] if a["status"] != "done"]
    log("Готово {} из {}; осталось примерно {}".format(len(done), len(plan["archives"]), human(
        sum(a["size"] for a in pending))))
    if plan["skipped"]:
        log("Пропущенные источники:")
        for item in plan["skipped"]:
            log("  {}: {}".format(item.get("archive_path", item["path"]), item["reason"]))


def scan_existing_sources(plan, log=print):
    files = []
    skipped = []

    def scan_root(root, arcname):
        def add(path, archive_path):
            try:
                st = os.lstat(str(path))
                logical = _logical_from_stat(path, archive_path, st)
                if logical["type"] == "file":
                    with open(str(path), "rb"):
                        pass
            except (OSError, ValueError) as e:
                skipped.append({"path": str(path), "archive_path": archive_path, "reason": str(e)})
                log("Пропущено {}: {}".format(path, e))
                return
            files.append(logical)
            if logical["type"] != "dir":
                return
            try:
                children = sorted(os.scandir(str(path)), key=lambda item: item.name)
            except OSError as e:
                skipped.append({"path": str(path), "archive_path": archive_path, "reason": str(e)})
                log("Не удалось прочитать папку {}: {}".format(path, e))
                return
            for child in children:
                add(Path(child.path), (PurePosixPath(archive_path) / child.name).as_posix())

        if not os.path.lexists(root):
            log("Источник сейчас недоступен, его старые записи сохранены: {}".format(root))
            return
        add(Path(root), arcname)

    for source in plan["sources"]:
        scan_root(source["path"], source["name"])
    return files, skipped


def planned_file_hash(out_dir, plan, logical):
    if logical.get("sha256"):
        return logical["sha256"]
    try:
        return hash_file(logical["source"])
    except OSError:
        pass
    stored = []
    for archive in plan["archives"]:
        for entry in archive["entries"]:
            if entry.get("source_path", entry["path"]) != logical["path"] or entry["type"] != "file":
                continue
            stored.append((archive, entry))
    if not stored:
        raise OSError("Нет данных для вычисления SHA256: {}".format(logical["path"]))
    stored.sort(key=lambda pair: pair[1].get("fragment", {}).get("index", 1))
    digest = hashlib.sha256()
    for archive, entry in stored:
        path = archive_path(out_dir, plan, archive["index"])
        with tarfile.open(str(path), "r:") as tar:
            member = tar.getmember(entry["path"])
            src = tar.extractfile(member)
            if src is None:
                raise OSError("Не удалось прочитать {}".format(path))
            while True:
                data = src.read(CHUNK)
                if not data:
                    break
                digest.update(data)
    return digest.hexdigest()


def validate_new_sources(plan, out_dir, paths):
    """Проверить новые корневые источники и вернуть записи для plan["sources"]."""
    tops = [Path(os.path.abspath(str(p))) for p in paths]
    out = Path(os.path.abspath(str(out_dir)))
    existing = [(s["path"], os.path.realpath(s["path"])) for s in plan["sources"]]
    used = {s["name"] for s in plan["sources"]}
    result = []
    taken = []
    for top in tops:
        if not os.path.lexists(str(top)):
            raise ValueError("Не найдено: {}".format(top))
        if os.path.isdir(str(top)) and not os.path.islink(str(top)) and _is_inside(out, top):
            raise ValueError("Папка результата не должна лежать внутри добавляемой папки: {}".format(top))
        real = os.path.realpath(str(top))
        for original, old_real in existing + taken:
            if real == old_real:
                raise ValueError("Уже входит в план: {}".format(top))
            if _is_inside(real, old_real):
                raise ValueError("{} уже лежит внутри {}: его файлы подхватит обычное «Добавить новое»".format(
                    top, original))
            if _is_inside(old_real, real):
                raise ValueError("{} содержит уже добавленный источник {}".format(top, original))
        taken.append((str(top), real))
        result.append({"path": str(top), "name": _duplicate_name(top.name or "archive", used)})
    return result


def _move_operations_and_sources(out_dir, plan, current, log=print, progress=None, cancel=None):
    previous = plan["files"]
    previous_sources = {f["source"] for f in previous}
    current_sources = {f["source"] for f in current}
    missing = [f for f in previous if f["source"] not in current_sources and f["type"] == "file"]
    added = [f for f in current if f["source"] not in previous_sources]
    candidates = [f for f in added if f["type"] == "file"]
    by_size = {}
    for item in candidates:
        by_size.setdefault(item["size"], []).append(item)
    paired = set()
    hashes = {}
    operations = []

    def digest(path):
        if path not in hashes:
            try:
                size = os.path.getsize(path)
            except OSError:
                size = 0
            if size >= HASH_LOG_THRESHOLD:
                log("Хэширование: {} ({})".format(path, human(size)))
            file_progress = (lambda done, size=size: progress(done, size)) if progress else None
            hashes[path] = hash_file(path, file_progress, cancel)
        return hashes[path]

    for old in sorted(missing, key=lambda f: f.get("current_path", f["path"])):
        try:
            old_digest = planned_file_hash(out_dir, plan, old)
        except OSError:
            continue
        for new in sorted(by_size.get(old["size"], []), key=lambda f: f["path"]):
            if new["source"] in paired:
                continue
            try:
                if digest(new["source"]) != old_digest:
                    continue
            except OSError:
                continue
            paired.add(new["source"])
            old_path = old.get("current_path", old["path"])
            operations.append({"type": "move", "source": old_path, "target": new["path"]})
            old["source"] = new["source"]
            old["current_path"] = new["path"]
            log("Перенос распознан по SHA256: {} -> {}".format(old_path, new["path"]))
            break
    new_entries = [f for f in added if f["source"] not in paired]
    for entry in new_entries:
        if entry["type"] == "file":
            entry["sha256"] = digest(entry["source"])
    return new_entries, operations


def _operation_archives(plan, operations, start_index, part_size):
    archives = []
    remaining = list(operations)
    while remaining:
        archive = _new_archive(start_index + len(archives))
        chunk = []
        for operation in remaining:
            archive["operations"] = chunk + [operation]
            if archive_estimate(plan, archive) <= part_size:
                chunk.append(operation)
            else:
                break
        if not chunk:
            raise ValueError("Операция переноса не помещается в архив: {}".format(remaining[0]["target"]))
        archive["operations"] = chunk
        _finish_archive(plan, archive, part_size)
        archives.append(archive)
        remaining = remaining[len(chunk):]
    return archives


def extend_plan(out_dir, name=None, max_parts=None, plan_only=False,
                log=print, progress=None, cancel=None, add_paths=None):
    out = Path(os.path.abspath(str(out_dir)))
    path = plan_path(out, name)
    with plan_lock(out, path.name[:-10]):
        plan = load_plan(path)
        added_sources = validate_new_sources(plan, out, add_paths) if add_paths else []
        plan["sources"].extend(added_sources)
        for source in added_sources:
            log("Новый корневой источник: {} -> {}".format(source["path"], source["name"]))
        log("Сканирование и вычисление SHA256 новых файлов…")
        current, skipped = scan_existing_sources(plan, log)
        new_entries, operations = _move_operations_and_sources(out, plan, current, log, progress, cancel)
        if not new_entries and not operations:
            log("Новых или перенесённых файлов не найдено")
            return plan
        old_count = len(plan["archives"])
        part_size = plan["parameters"]["part_size"]
        packing_plan = dict(plan)
        packing_plan["files"] = new_entries
        new_archives = pack_entries(packing_plan, part_size)
        new_archives.extend(_operation_archives(plan, operations, old_count + len(new_archives) + 1, part_size))
        for offset, archive in enumerate(new_archives, old_count + 1):
            archive["index"] = offset
        total = old_count + len(new_archives)
        for archive in plan["archives"] + new_archives:
            archive["total_archives"] = total
        plan["files"].extend(new_entries)
        plan["archives"].extend(new_archives)
        known_skipped = {item["path"] for item in plan["skipped"]}
        plan["skipped"].extend(item for item in skipped if item["path"] not in known_skipped)
        extension = {"number": len(plan.get("extensions", [])) + 1,
                     "archives": [a["index"] for a in new_archives],
                     "added": [f["path"] for f in new_entries], "moves": operations}
        if added_sources:
            extension["sources"] = added_sources
        plan.setdefault("extensions", []).append(extension)
        atomic_json(path, plan)
        log("План расширен: новых элементов {}, переносов {}, новых архивов {}".format(
            len(new_entries), len(operations), len(new_archives)))
        if plan_only:
            log("Новые архивы не создавались: указан --plan-only")
            return plan
        indices = extension["archives"]
        if max_parts is not None:
            if max_parts < 1:
                raise ValueError("--max-parts должен быть положительным")
            indices = indices[:max_parts]
        check_possible_renames(plan, indices)
        try:
            for index in indices:
                build_archive(plan, out, index, progress, cancel, log)
        except (Cancelled, KeyboardInterrupt):
            log("Отменено: готово {} из {}, запустите split снова для продолжения".format(
                sum(a["status"] == "done" for a in plan["archives"]), total))
            raise Cancelled()
        return plan


def make_tarinfo(entry):
    info = tarfile.TarInfo(entry["path"])
    info.uid = info.gid = 0
    info.uname = info.gname = ""
    info.mtime = int(entry.get("mtime", 0))
    info.mode = int(entry.get("mode", 0o644))
    if entry["type"] == "file":
        info.type = tarfile.REGTYPE
        info.size = int(entry["size"])
    elif entry["type"] == "dir":
        info.type = tarfile.DIRTYPE
        info.size = 0
    elif entry["type"] == "symlink":
        info.type = tarfile.SYMTYPE
        info.size = 0
        info.linkname = entry.get("linkname", "")
    else:
        raise ValueError("Неподдерживаемый тип в плане: {}".format(entry["type"]))
    return info


class HashingWriter:
    def __init__(self, fileobj, capacity):
        self.fileobj = fileobj
        self.capacity = capacity
        self.count = 0
        self.sha256 = hashlib.sha256()

    def write(self, data):
        data = bytes(data)
        if self.count + len(data) > self.capacity:
            raise IntegrityError("Реальный размер архива превысил {}".format(human(self.capacity)))
        written = self.fileobj.write(data)
        if written is not None and written != len(data):
            raise OSError("Не удалось записать архив целиком")
        self.count += len(data)
        self.sha256.update(data)
        return len(data)

    def flush(self):
        self.fileobj.flush()

    def finish(self):
        self.fileobj.flush()
        os.fsync(self.fileobj.fileno())
        self.fileobj.close()


class EntryReader:
    def __init__(self, fileobj, length, offset=0, progress=None, cancel=None):
        self.fileobj = fileobj
        self.remaining = length
        self.offset = offset
        self.progress = progress
        self.cancel = cancel
        self.sha256 = hashlib.sha256()
        self.done = 0
        if offset:
            fileobj.seek(offset)

    def read(self, size=-1):
        if self.cancel is not None and self.cancel.is_set():
            raise Cancelled()
        if self.remaining <= 0:
            return b""
        if size is None or size < 0 or size > self.remaining:
            size = self.remaining
        data = self.fileobj.read(min(size, CHUNK))
        if not data:
            raise IntegrityError("Файл закончился раньше, чем указано в плане")
        self.remaining -= len(data)
        self.done += len(data)
        self.sha256.update(data)
        if self.progress:
            self.progress(self.done, self.done + self.remaining)
        return data


def source_map(plan):
    return {f["path"]: f for f in plan["files"]}


def missing_sources(files, archive):
    """Логические пути файлов архива, которых больше нет на диске (удалены пользователем)."""
    result = []
    for entry in archive["entries"]:
        if entry["type"] != "file":
            continue
        logical_path = entry.get("source_path", entry["path"])
        logical = files.get(logical_path)
        if logical is None or logical_path in result:
            continue
        if not os.path.lexists(logical["source"]):
            result.append(logical_path)
    return result


def check_sources(plan, archive, when="перед записью"):
    files = source_map(plan)
    errors = []
    checked = set()
    for entry in archive["entries"]:
        if entry["type"] != "file":
            continue
        logical_path = entry.get("source_path", entry["path"])
        if logical_path in checked:
            continue
        checked.add(logical_path)
        logical = files.get(logical_path)
        if logical is None:
            errors.append("{}: нет в плане".format(logical_path))
            continue
        try:
            st = os.stat(logical["source"])
            if not stat.S_ISREG(st.st_mode):
                raise OSError("больше не является обычным файлом")
            if st.st_size != logical["size"] or st.st_mtime_ns != logical["mtime_ns"]:
                errors.append("{}: размер/mtime изменились ({} {}, ожидалось {} {})".format(
                    logical["source"], st.st_size, st.st_mtime_ns, logical["size"], logical["mtime_ns"]))
                continue
            with open(logical["source"], "rb"):
                pass
        except OSError as e:
            errors.append("{}: {}".format(logical["source"], e))
    if errors:
        raise IntegrityError("Источники изменились или недоступны ({}):\n  {}".format(when, "\n  ".join(errors)))


def archive_path(out, plan, index):
    return Path(out) / "{}.{:04d}.tar".format(plan["name"], index)


def write_entries_hash(tar, hashes):
    lines = ["{}  {}\n".format(hashes[e["path"]], e["path"]) for e in hashes["order"]]
    data = "".join(lines).encode("utf-8", "surrogateescape")
    info = make_tarinfo({"path": ".tgsplit/entries.sha256", "type": "file", "size": len(data),
                         "mode": 0o644, "mtime": 0})
    tar.addfile(info, io.BytesIO(data))


def build_archive(plan, out_dir, index, progress=None, cancel=None, log=print):
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    archive = plan["archives"][index - 1]
    if archive["index"] != index:
        raise ValueError("Нарушена нумерация архивов")
    files = source_map(plan)
    missing = missing_sources(files, archive)
    if missing:
        log("Архив {:04d}: отсутствуют файлы, они будут пропущены ({}):".format(index, len(missing)))
        for logical_path in missing[:10]:
            log("  нет файла: {}".format(logical_path))
        if len(missing) > 10:
            log("  … и ещё {}".format(len(missing) - 10))
        skip = set(missing)
        stored = dict(archive)
        stored["entries"] = [e for e in archive["entries"]
                             if e["type"] != "file" or e.get("source_path", e["path"]) not in skip]
        # Для файлов, разрезанных на фрагменты, при восстановлении нужно знать,
        # что файл удалён намеренно, а не что часть архивов потеряна.
        omitted = []
        for e in archive["entries"]:
            logical_path = e.get("source_path")
            if e["type"] == "file" and "fragment" in e and logical_path in skip and logical_path not in omitted:
                omitted.append(logical_path)
        if omitted:
            stored["omitted"] = omitted
    else:
        stored = archive
    check_sources(plan, stored, "предварительная проверка")
    free = shutil.disk_usage(str(out)).free
    if free < archive["size"]:
        raise OSError("Не хватает места для одного архива: нужно {}, свободно {}".format(
            human(archive["size"]), human(free)))
    target = archive_path(out, plan, index)
    part = Path(str(target) + ".part")
    hashes = {"order": stored["entries"]}
    raw = open(str(part), "wb", buffering=0)
    writer = HashingWriter(raw, plan["parameters"]["part_size"])
    tar = None
    renamed = False
    try:
        tar = tarfile.open(fileobj=writer, mode="w|", format=tarfile.PAX_FORMAT, bufsize=CHUNK)
        if hasattr(tar, "copybufsize"):
            tar.copybufsize = CHUNK
        manifest = canonical_json(manifest_for_archive(plan, stored))
        info = make_tarinfo({"path": ".tgsplit/manifest.json", "type": "file", "size": len(manifest),
                             "mode": 0o644, "mtime": 0})
        tar.addfile(info, io.BytesIO(manifest))
        total = sum(e["size"] for e in stored["entries"] if e["type"] == "file")
        tracker = {"done": 0}

        def entry_progress(done, entry_total):
            if progress:
                progress(tracker["done"] + done, total)

        for entry in stored["entries"]:
            info = make_tarinfo(entry)
            if entry["type"] != "file":
                tar.addfile(info)
                hashes[entry["path"]] = hashlib.sha256(b"").hexdigest()
                continue
            logical = files[entry.get("source_path", entry["path"])]
            fragment = entry.get("fragment")
            offset = fragment["offset"] if fragment else 0
            with open(logical["source"], "rb") as f:
                reader = EntryReader(f, entry["size"], offset, entry_progress, cancel)
                tar.addfile(info, reader)
                if reader.remaining:
                    raise IntegrityError("Не весь файл записан: {}".format(logical["source"]))
                hashes[entry["path"]] = reader.sha256.hexdigest()
            tracker["done"] += entry["size"]
            if progress:
                progress(tracker["done"], total)
        write_entries_hash(tar, hashes)
        tar.close()
        tar = None
        check_sources(plan, stored, "после записи")
        writer.finish()
        os.replace(str(part), str(target))
        renamed = True
        digest = writer.sha256.hexdigest()
        atomic_bytes(Path(str(target) + ".sha256"),
                     "{}  {}\n".format(digest, target.name).encode("utf-8"))
        archive["sha256"] = digest
        archive["size"] = writer.count
        archive["status"] = "done"
        atomic_json(out / "{}.plan.json".format(plan["name"]), plan)
        if progress:
            progress(total, total)
        log("Готово: {} ({})".format(target.name, human(writer.count)))
        return target
    except BaseException:
        if tar is not None:
            try:
                tar.close()
            except Exception:
                pass
        try:
            raw.close()
        except OSError:
            pass
        if not renamed:
            try:
                part.unlink()
            except OSError:
                pass
        raise


def load_restore_state(out_dir):
    path = Path(out_dir) / RESTORE_STATE
    if not path.exists():
        return None
    with open(str(path), "r", encoding="utf-8") as f:
        return json.load(f)


def new_restore_state(plan_id, total_archives):
    return {"format": 1, "plan_id": plan_id, "total_archives": total_archives,
            "archives": [], "files": {}, "directories": {}, "moves": []}


def safe_archive_path(name):
    if not isinstance(name, str) or not name or "\\" in name:
        raise ValueError("Небезопасный путь в архиве: {!r}".format(name))
    pure = PurePosixPath(name)
    if pure.is_absolute() or any(p in ("", "..") for p in pure.parts):
        raise ValueError("Небезопасный путь в архиве: {}".format(name))
    if Path(name).drive or Path(name).is_absolute() or (len(name) > 1 and name[1] == ":"):
        raise ValueError("Абсолютный путь в архиве запрещён: {}".format(name))
    if any(p == "." for p in pure.parts):
        raise ValueError("Небезопасный путь в архиве: {}".format(name))
    return pure.parts


def safe_target(root, name, create_parent=True):
    parts = safe_archive_path(name)
    target = Path(root).joinpath(*parts)
    parent = Path(root)
    for part in parts[:-1] if create_parent else ():
        parent = parent / part
        if os.path.lexists(str(parent)):
            if parent.is_symlink() or not parent.is_dir():
                raise ValueError("Путь выходит через ссылку или непапку: {}".format(name))
        else:
            parent.mkdir()
    if os.path.realpath(str(target.parent)) != os.path.realpath(str(root)) and not _is_inside(target.parent, root):
        raise ValueError("Путь выходит за папку восстановления: {}".format(name))
    return target


def choose_existing(path, on_exist):
    if not os.path.lexists(str(path)):
        return path
    if on_exist == "skip":
        return None
    if on_exist == "overwrite":
        return path
    if on_exist != "rename":
        raise ValueError("Неизвестный режим --on-exist: {}".format(on_exist))
    number = 2
    while True:
        candidate = Path("{}_{}".format(path, number))
        if not os.path.lexists(str(candidate)):
            return candidate
        number += 1


def copy_exact(src, dst, length, progress=None, cancel=None):
    remaining = length
    digest = hashlib.sha256()
    done = 0
    while remaining:
        if cancel is not None and cancel.is_set():
            raise Cancelled()
        data = src.read(min(CHUNK, remaining))
        if not data:
            raise IntegrityError("Неожиданный конец элемента архива")
        if dst is not None:
            dst.write(data)
        digest.update(data)
        remaining -= len(data)
        done += len(data)
        if progress:
            progress(done, length)
    return digest.hexdigest()


def apply_file_attributes(path, mode, mtime):
    try:
        os.chmod(str(path), mode)
    except OSError:
        pass
    os.utime(str(path), (int(mtime), int(mtime)))


def extract_whole_member(tar, member, entry, root, on_exist, cancel=None):
    target = safe_target(root, entry["path"])
    destination = choose_existing(target, on_exist)
    src = tar.extractfile(member)
    if src is None:
        raise IntegrityError("Не удалось прочитать {}".format(entry["path"]))
    if destination is None:
        return copy_exact(src, None, member.size, cancel=cancel), target, True
    fd, tmp = tempfile.mkstemp(prefix=".tgsplit-", dir=str(destination.parent))
    try:
        with os.fdopen(fd, "wb") as out:
            digest = copy_exact(src, out, member.size, cancel=cancel)
            out.flush()
            os.fsync(out.fileno())
        if on_exist == "overwrite" and os.path.isdir(str(destination)) and not destination.is_symlink():
            raise ValueError("Нельзя заменить папку файлом: {}".format(destination))
        os.replace(tmp, str(destination))
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise
    apply_file_attributes(destination, entry["mode"], entry["mtime"])
    return digest, destination, False


def extract_symlink_member(entry, root, on_exist):
    link = entry.get("linkname", "")
    if os.path.isabs(link) or (len(link) > 1 and link[1] == ":") or ".." in PurePosixPath(link.replace("\\", "/")).parts:
        raise ValueError("Небезопасная символическая ссылка: {} -> {}".format(entry["path"], link))
    target = safe_target(root, entry["path"])
    destination = choose_existing(target, on_exist)
    if destination is None:
        return target, True
    if on_exist == "overwrite" and os.path.lexists(str(destination)):
        if destination.is_dir() and not destination.is_symlink():
            raise ValueError("Нельзя заменить папку ссылкой: {}".format(destination))
        destination.unlink()
    os.symlink(link, str(destination))
    return destination, False


def drop_omitted(root, state, omitted, log=print):
    """Файл удалён до создания части архивов: убрать недособранный файл и не восстанавливать его."""
    known = state.setdefault("omitted", [])
    for logical in omitted:
        if logical not in known:
            known.append(logical)
        record = state["files"].get(logical)
        if record is None or record.get("kind") != "fragments" or record.get("status") == "done":
            continue
        partial = Path(str(safe_target(root, logical, create_parent=False)) + ".tgspart")
        try:
            partial.unlink()
        except OSError:
            pass
        del state["files"][logical]
        log("Файл был удалён до создания части архивов, недособранный файл убран: {}".format(logical))


def extract_fragment_member(tar, member, entry, root, state, cancel=None):
    logical = entry.get("source_path")
    frag = entry.get("fragment")
    if not logical or not frag:
        raise ValueError("Некорректный фрагмент в манифесте: {}".format(entry["path"]))
    required = {"index", "count", "offset", "length", "total_size"}
    if not required.issubset(frag) or frag["length"] != member.size:
        raise ValueError("Некорректные параметры фрагмента: {}".format(entry["path"]))
    if frag["index"] < 1 or frag["index"] > frag["count"] or frag["offset"] < 0 or frag["length"] < 0:
        raise ValueError("Некорректные границы фрагмента: {}".format(entry["path"]))
    if frag["offset"] + frag["length"] > frag["total_size"]:
        raise ValueError("Фрагмент выходит за размер файла: {}".format(entry["path"]))
    if logical in state.get("omitted", []):
        src = tar.extractfile(member)
        if src is None:
            raise IntegrityError("Не удалось прочитать {}".format(entry["path"]))
        return copy_exact(src, None, member.size, cancel=cancel)
    record = state["files"].get(logical)
    if record is None:
        record = {"kind": "fragments", "count": frag["count"], "total_size": frag["total_size"],
                  "mode": entry["mode"], "mtime": entry["mtime"], "fragments": {}, "status": "partial"}
        state["files"][logical] = record
    if (record.get("kind") != "fragments" or record.get("count") != frag["count"] or
            record.get("total_size") != frag["total_size"]):
        raise ValueError("Противоречивые фрагменты файла: {}".format(logical))
    if record.get("status") == "done":
        src = tar.extractfile(member)
        if src is None:
            raise IntegrityError("Не удалось прочитать {}".format(entry["path"]))
        return copy_exact(src, None, member.size, cancel=cancel)
    number = str(frag["index"])
    old = record["fragments"].get(number)
    current = {"offset": frag["offset"], "length": frag["length"]}
    if old is not None and old != current:
        raise ValueError("Фрагмент повторился с другими параметрами: {}".format(entry["path"]))
    target = safe_target(root, logical)
    partial = Path(str(target) + ".tgspart")
    if os.path.lexists(str(partial)) and partial.is_symlink():
        raise ValueError("Временный файл является ссылкой: {}".format(partial))
    src = tar.extractfile(member)
    if src is None:
        raise IntegrityError("Не удалось прочитать {}".format(entry["path"]))
    with open(str(partial), "r+b" if partial.exists() else "w+b") as out:
        out.seek(frag["offset"])
        digest = copy_exact(src, out, frag["length"], cancel=cancel)
        out.flush()
    record["fragments"][number] = current
    return digest


def finalize_fragments(root, state, on_exist):
    for logical, record in state["files"].items():
        if record.get("kind") != "fragments" or record.get("status") == "done":
            continue
        if len(record["fragments"]) != record["count"]:
            continue
        expected = {str(i) for i in range(1, record["count"] + 1)}
        if set(record["fragments"]) != expected:
            continue
        target = safe_target(root, logical)
        partial = Path(str(target) + ".tgspart")
        if not partial.is_file() or partial.stat().st_size != record["total_size"]:
            raise IntegrityError("Неполный размер собранного файла: {}".format(logical))
        destination = choose_existing(target, on_exist)
        if destination is not None:
            if on_exist == "overwrite" and destination.is_dir() and not destination.is_symlink():
                raise ValueError("Нельзя заменить папку файлом: {}".format(destination))
            os.replace(str(partial), str(destination))
            apply_file_attributes(destination, record["mode"], record["mtime"])
        else:
            destination = target
        record["status"] = "done"
        record["restored_path"] = str(destination.relative_to(root))


def apply_moves(root, state, on_exist, log=print):
    moves = state.get("moves", [])
    applied = state.setdefault("applied_moves", [])
    for unused in range(len(moves)):
        changed = False
        for operation in moves:
            if operation in applied:
                continue
            old = operation["source"]
            new = operation["target"]
            record = None
            record_key = old
            for path, candidate in state["files"].items():
                if path == old or candidate.get("logical_path", path) == old:
                    record = candidate
                    record_key = path
                    break
            if record is not None and record.get("logical_path", record_key) == new:
                continue
            if record is not None and record.get("status") != "done":
                continue
            current = record.get("current_path", record_key) if record is not None else old
            source = safe_target(root, current, create_parent=False)
            if not os.path.lexists(str(source)):
                continue
            if source.is_dir() and not source.is_symlink():
                raise ValueError("Операция move поддерживает только файлы: {}".format(old))
            target = safe_target(root, new)
            destination = choose_existing(target, on_exist)
            if destination is None:
                log("Перенос пропущен, файл назначения существует: {}".format(new))
                continue
            os.replace(str(source), str(destination))
            if record is None:
                record = {"kind": "whole", "status": "done"}
                state["files"][record_key] = record
            record["logical_path"] = new
            record["current_path"] = destination.relative_to(root).as_posix()
            record["restored_path"] = record["current_path"]
            applied.append(operation)
            log("Восстановлен перенос: {} -> {}".format(old, new))
            changed = True
        if not changed:
            break


def format_ranges(numbers):
    numbers = sorted(set(numbers))
    if not numbers:
        return "нет"
    ranges = []
    start = prev = numbers[0]
    for n in numbers[1:]:
        if n == prev + 1:
            prev = n
            continue
        ranges.append(str(start) if start == prev else "{}-{}".format(start, prev))
        start = prev = n
    ranges.append(str(start) if start == prev else "{}-{}".format(start, prev))
    return ",".join(ranges)


def restore_report(root, state, log=print):
    complete = sorted(r.get("current_path", p) for p, r in state["files"].items() if r.get("status") == "done")
    incomplete = []
    for path, record in sorted(state["files"].items()):
        if record.get("kind") == "fragments" and record.get("status") != "done":
            missing = [i for i in range(1, record["count"] + 1) if str(i) not in record["fragments"]]
            incomplete.append({"path": record.get("current_path", path), "missing": missing})
    log("Получены архивы {} из {}; полностью восстановлено файлов: {}; неполных: {}".format(
        format_ranges(state["archives"]), state["total_archives"], len(complete), len(incomplete)))
    if state.get("omitted"):
        log("Файлов, удалённых до создания архивов (пропущены): {}".format(len(state["omitted"])))
    for item in incomplete:
        log("  Неполный {}: нет фрагментов {}".format(item["path"],
            ",".join(str(i) for i in item["missing"])))
    return {"complete": complete, "incomplete": incomplete, "archives": sorted(state["archives"]),
            "total_archives": state["total_archives"], "plan_id": state["plan_id"]}


class HashingReader:
    def __init__(self, fileobj, progress=None, cancel=None):
        self.fileobj = fileobj
        self.sha256 = hashlib.sha256()
        self.count = 0
        self.progress = progress
        self.cancel = cancel

    def read(self, size=-1):
        if self.cancel is not None and self.cancel.is_set():
            raise Cancelled()
        if size is None or size < 0:
            size = CHUNK
        data = self.fileobj.read(min(size, CHUNK))
        if data:
            self.sha256.update(data)
            self.count += len(data)
            if self.progress:
                self.progress(self.count, max(self.count, 1))
        return data

    def drain(self):
        while self.read(CHUNK):
            pass


def member_data(tar, member, limit=128 * MiB):
    if member.size > limit:
        raise ValueError("Служебный элемент слишком большой: {}".format(member.name))
    src = tar.extractfile(member)
    if src is None:
        raise IntegrityError("Не удалось прочитать {}".format(member.name))
    data = src.read(member.size)
    if len(data) != member.size:
        raise IntegrityError("Повреждён служебный элемент {}".format(member.name))
    return data


def expected_entry_hash(entry, digest):
    return hashlib.sha256(b"").hexdigest() if entry["type"] != "file" else digest


def check_entries_hash(data, entries, hashes):
    try:
        text = data.decode("utf-8", "surrogateescape")
        lines = text.splitlines()
        parsed = {}
        order = []
        for line in lines:
            digest, path = line.split("  ", 1)
            parsed[path] = digest
            order.append(path)
        expected_order = [e["path"] for e in entries]
        if order != expected_order:
            raise ValueError("порядок хэшей отличается")
        for entry in entries:
            if parsed[entry["path"]].lower() != hashes[entry["path"]]:
                raise IntegrityError("Хэш содержимого не совпал: {}".format(entry["path"]))
    except (UnicodeError, ValueError, KeyError) as e:
        if isinstance(e, IntegrityError):
            raise
        raise IntegrityError("Повреждён .tgsplit/entries.sha256: {}".format(e))


def extract_foreign_member(tar, member, root, on_exist, directories, cancel=None):
    entry = {"path": member.name.rstrip("/"), "mode": member.mode, "mtime": int(member.mtime)}
    if member.isdir():
        target = safe_target(root, entry["path"])
        if os.path.lexists(str(target)) and (target.is_symlink() or not target.is_dir()):
            raise ValueError("Конфликт папки: {}".format(target))
        target.mkdir(exist_ok=True)
        directories.append(entry)
    elif member.isreg():
        entry.update(type="file", size=member.size)
        extract_whole_member(tar, member, entry, root, on_exist, cancel)
    elif member.issym():
        entry.update(type="symlink", linkname=member.linkname)
        extract_symlink_member(entry, root, on_exist)
    elif member.islnk():
        source = safe_target(root, member.linkname, create_parent=False)
        if not source.is_file() or source.is_symlink():
            raise ValueError("Небезопасная жёсткая ссылка: {}".format(member.name))
        target = safe_target(root, entry["path"])
        destination = choose_existing(target, on_exist)
        if destination is not None:
            fd, tmp = tempfile.mkstemp(prefix=".tgsplit-", dir=str(destination.parent))
            with os.fdopen(fd, "wb") as out, open(str(source), "rb") as src:
                shutil.copyfileobj(src, out, CHUNK)
            os.replace(tmp, str(destination))
            apply_file_attributes(destination, member.mode, member.mtime)
    else:
        raise ValueError("Неподдерживаемый или небезопасный тип члена TAR: {}".format(member.name))


def process_new_archive(path, root, state, on_exist, log=print, progress=None, cancel=None):
    reader = HashingReader(open(str(path), "rb"), progress, cancel)
    tar = None
    try:
        tar = tarfile.open(fileobj=reader, mode="r|*", bufsize=CHUNK)
        first = tar.next()
        if first is None:
            raise IntegrityError("Пустой архив: {}".format(path))
        if first.name != ".tgsplit/manifest.json":
            directories = []
            extract_foreign_member(tar, first, root, on_exist, directories, cancel)
            for member in tar:
                extract_foreign_member(tar, member, root, on_exist, directories, cancel)
            for entry in sorted(directories, key=lambda e: len(e["path"].split("/")), reverse=True):
                apply_file_attributes(safe_target(root, entry["path"], False), entry["mode"], entry["mtime"])
            tar.close()
            tar = None
            reader.drain()
            return {"manifest": None, "sha256": reader.sha256.hexdigest()}
        manifest = json.loads(member_data(tar, first).decode("utf-8"))
        if manifest.get("format") != FORMAT_VERSION:
            raise ValueError("Неподдерживаемый формат манифеста: {}".format(path))
        if state["plan_id"] != manifest.get("plan_id"):
            raise ValueError("Смешивать архивы разных plan_id нельзя")
        entries = manifest.get("entries")
        if not isinstance(entries, list):
            raise ValueError("В манифесте нет списка entries")
        index = int(manifest.get("archive"))
        archive_total = int(manifest.get("total_archives"))
        if index < 1 or archive_total < index:
            raise ValueError("Некорректная нумерация в манифесте: {}".format(path))
        operations = manifest.get("operations", [])
        if not isinstance(operations, list):
            raise ValueError("Некорректный список операций: {}".format(path.name))
        for operation in operations:
            if not isinstance(operation, dict) or operation.get("type") != "move":
                raise ValueError("Неизвестная операция в манифесте: {}".format(path.name))
            safe_archive_path(operation.get("source"))
            safe_archive_path(operation.get("target"))
        omitted = manifest.get("omitted", [])
        if not isinstance(omitted, list):
            raise ValueError("Некорректный список omitted: {}".format(path.name))
        for logical_path in omitted:
            safe_archive_path(logical_path)
        hashes = {}
        directories = []
        if omitted:
            drop_omitted(root, state, omitted, log)
        for entry in entries:
            member = tar.next()
            if member is None or member.name != entry.get("path"):
                raise IntegrityError("Порядок членов не совпадает с манифестом: {}".format(path.name))
            kind = entry.get("type")
            if kind == "file" and not member.isreg():
                raise IntegrityError("Тип члена не совпадает с манифестом: {}".format(member.name))
            if kind == "dir" and not member.isdir():
                raise IntegrityError("Тип члена не совпадает с манифестом: {}".format(member.name))
            if kind == "symlink" and not member.issym():
                raise IntegrityError("Тип члена не совпадает с манифестом: {}".format(member.name))
            if member.size != entry.get("size"):
                raise IntegrityError("Размер члена не совпадает с манифестом: {}".format(member.name))
            if kind == "file" and "fragment" in entry:
                digest = extract_fragment_member(tar, member, entry, root, state, cancel)
            elif kind == "file":
                digest, destination, skipped = extract_whole_member(tar, member, entry, root, on_exist, cancel)
                state["files"][entry["path"]] = {
                    "kind": "whole", "status": "done", "restored_path": str(destination.relative_to(root)),
                    "skipped": skipped,
                }
            elif kind == "dir":
                target = safe_target(root, entry["path"])
                if os.path.lexists(str(target)) and (target.is_symlink() or not target.is_dir()):
                    raise ValueError("Конфликт папки: {}".format(target))
                target.mkdir(exist_ok=True)
                directories.append(entry)
                state.setdefault("directories", {})[entry["path"]] = entry
                digest = hashlib.sha256(b"").hexdigest()
            elif kind == "symlink":
                extract_symlink_member(entry, root, on_exist)
                digest = hashlib.sha256(b"").hexdigest()
            else:
                raise ValueError("Неизвестный тип в манифесте: {}".format(kind))
            hashes[entry["path"]] = expected_entry_hash(entry, digest)
        last = tar.next()
        if last is None or last.name != ".tgsplit/entries.sha256" or not last.isreg():
            raise IntegrityError("Нет завершающего .tgsplit/entries.sha256: {}".format(path.name))
        check_entries_hash(member_data(tar, last), entries, hashes)
        if tar.next() is not None:
            raise IntegrityError("После entries.sha256 есть лишние члены: {}".format(path.name))
        tar.close()
        tar = None
        reader.drain()
        if index not in state["archives"]:
            state["archives"].append(index)
        state["total_archives"] = max(state["total_archives"], archive_total)
        moves = state.setdefault("moves", [])
        for operation in operations:
            if operation not in moves:
                moves.append(operation)
        finalize_fragments(root, state, on_exist)
        apply_moves(root, state, on_exist, log)
        all_directories = state.setdefault("directories", {})
        for entry in sorted(all_directories.values(), key=lambda e: len(e["path"].split("/")), reverse=True):
            apply_file_attributes(safe_target(root, entry["path"], False), entry["mode"], entry["mtime"])
        return {"manifest": manifest, "sha256": reader.sha256.hexdigest()}
    finally:
        if tar is not None:
            tar.close()
        reader.fileobj.close()


def collect_archives(inputs):
    result = []
    for item in inputs:
        path = Path(os.path.abspath(str(item)))
        if path.is_dir():
            result.extend(p for p in path.iterdir() if p.is_file() and p.suffix.lower() == ".tar")
        elif path.is_file():
            result.append(path)
        else:
            raise ValueError("Не найдено: {}".format(path))
    unique = []
    seen = set()
    for path in result:
        key = os.path.normcase(os.path.abspath(str(path)))
        if key not in seen:
            seen.add(key)
            unique.append(path)
    if not unique:
        raise ValueError("TAR-архивы не найдены")
    return sorted(unique, key=lambda p: p.name)


def archive_sidecar_hash(path):
    sidecar = Path(str(path) + ".sha256")
    try:
        text = sidecar.read_text(encoding="utf-8")
        digest, filename = text.strip().split(None, 1)
        if filename.strip() != path.name or len(digest) != 64:
            raise ValueError
        int(digest, 16)
        return digest.lower()
    except (OSError, ValueError, UnicodeError):
        return None


def restore_archives(inputs, out_dir=None, on_exist="skip", keep_partial=True,
                     log=print, progress=None, cancel=None):
    archives = collect_archives(inputs)
    root = Path(os.path.abspath(str(out_dir))) if out_dir else archives[0].parent / "restored"
    root.mkdir(parents=True, exist_ok=True)
    state = load_restore_state(root)
    report = None
    for path in archives:
        expected = archive_sidecar_hash(path)
        if expected is None:
            log("ВНИМАНИЕ: нет или повреждён файл {}.sha256".format(path.name))
        try:
            if state is None:
                probe = HashingReader(open(str(path), "rb"))
                probe_tar = None
                try:
                    probe_tar = tarfile.open(fileobj=probe, mode="r|*", bufsize=CHUNK)
                    first = probe_tar.next()
                    if first is not None and first.name == ".tgsplit/manifest.json":
                        manifest = json.loads(member_data(probe_tar, first).decode("utf-8"))
                        state = new_restore_state(manifest["plan_id"], manifest["total_archives"])
                    else:
                        state = new_restore_state("foreign", 0)
                finally:
                    if probe_tar is not None:
                        probe_tar.close()
                    probe.fileobj.close()
            log("Восстановление: {}".format(path.name))
            result = process_new_archive(path, root, state, on_exist, log, progress, cancel)
        except (ValueError, KeyError, tarfile.TarError) as e:
            if expected is not None and hash_file(path) != expected:
                log("ВНИМАНИЕ: архив {} повреждён; ничего не удалено".format(path.name))
                raise IntegrityError("Архив не прошёл проверку SHA256: {}".format(path.name))
            if isinstance(e, KeyError):
                raise ValueError("Некорректный манифест {}: нет ключа {}".format(path.name, e))
            raise
        if result["manifest"] is not None:
            atomic_json(root / RESTORE_STATE, state)
            report = restore_report(root, state, log)
        if expected is not None and result["sha256"] != expected:
            log("ВНИМАНИЕ: SHA256 архива {} НЕ СОВПАЛ; ничего не удалено".format(path.name))
            raise IntegrityError("Контрольная сумма архива не совпала: {}".format(path.name))
    if report is None and state is not None and state["plan_id"] != "foreign":
        report = restore_report(root, state, log)
    if not keep_partial and report is not None:
        for item in report["incomplete"]:
            target = safe_target(root, item["path"])
            partial = Path(str(target) + ".tgspart")
            try:
                partial.unlink()
            except OSError:
                pass
            state["files"][item["path"]]["fragments"] = {}
        atomic_json(root / RESTORE_STATE, state)
    return report


def hash_file(path, progress=None, cancel=None):
    digest = hashlib.sha256()
    done = 0
    with open(str(path), "rb") as f:
        while True:
            if cancel is not None and cancel.is_set():
                raise Cancelled()
            data = f.read(CHUNK)
            if not data:
                break
            digest.update(data)
            done += len(data)
            if progress is not None:
                progress(done)
    return digest.hexdigest()


def verify_archives(out_dir, name=None, log=print):
    plan = load_plan(out_dir, name)
    out = plan_path(out_dir, name).parent
    checked = 0
    for archive in plan["archives"]:
        path = archive_path(out, plan, archive["index"])
        if not path.is_file():
            continue
        expected = archive_sidecar_hash(path)
        if expected is None:
            log("ВНИМАНИЕ: нет или повреждён файл {}.sha256".format(path.name))
            continue
        actual = hash_file(path)
        if actual != expected:
            raise IntegrityError("Контрольная сумма не совпала: {}".format(path.name))
        if archive.get("sha256") and archive["sha256"] != actual:
            raise IntegrityError("Архив не совпадает с планом: {}".format(path.name))
        checked += 1
        log("OK: {}".format(path.name))
    log("Проверено присутствующих архивов: {}".format(checked))
    return checked


class LegacyJoinReader:
    def __init__(self, parts, progress=None, cancel=None):
        self.parts = parts
        self.progress = progress
        self.cancel = cancel
        self.index = 0
        self.fileobj = None
        self.sha256 = hashlib.sha256()
        self.done = 0
        self.total = sum(p.stat().st_size for p in parts)

    def read(self, size=-1):
        if self.cancel is not None and self.cancel.is_set():
            raise Cancelled()
        if size is None or size < 0:
            size = CHUNK
        chunks = []
        remaining = size
        while remaining:
            if self.fileobj is None:
                if self.index >= len(self.parts):
                    break
                self.fileobj = open(str(self.parts[self.index]), "rb")
                self.index += 1
            data = self.fileobj.read(min(remaining, CHUNK))
            if not data:
                self.fileobj.close()
                self.fileobj = None
                continue
            chunks.append(data)
            remaining -= len(data)
            self.sha256.update(data)
            self.done += len(data)
            if self.progress:
                self.progress(self.done, self.total)
        return b"".join(chunks)

    def close(self):
        if self.fileobj is not None:
            self.fileobj.close()
            self.fileobj = None


def find_legacy_groups(path, log=print):
    path = Path(os.path.abspath(str(path)))
    folder = path if path.is_dir() else path.parent
    strict = path.is_file()
    if not path.exists():
        raise ValueError("Не найдено: {}".format(path))
    groups = {}
    for item in folder.iterdir():
        match = PART_RE.match(item.name)
        if match and item.is_file():
            groups.setdefault(match["base"], {})[int(match["num"])] = item
    if strict:
        match = PART_RE.match(path.name)
        if not match:
            raise ValueError("Ожидается часть name.tar.001 или папка")
        groups = {match["base"]: groups.get(match["base"], {})}
    result = []
    for base, numbered in sorted(groups.items()):
        if 1 not in numbered:
            if strict:
                raise ValueError("«{}»: нет части .001".format(base))
            continue
        top = max(numbered)
        missing = [i for i in range(1, top + 1) if i not in numbered]
        if missing:
            raise ValueError("«{}»: не хватает частей {}".format(base, missing))
        result.append((base, [numbered[i] for i in range(1, top + 1)]))
    if not result:
        raise ValueError("Старые части .001 не найдены")
    return result


def legacy_expected_hash(parts, base):
    try:
        return (parts[0].parent / (base + ".sha256")).read_text(encoding="utf-8").split()[0].lower()
    except (OSError, IndexError, UnicodeError):
        return None


def join_legacy_one(base, parts, out_dir, merge_only=False, log=print, progress=None, cancel=None):
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    reader = LegacyJoinReader(parts, progress, cancel)
    expected = legacy_expected_hash(parts, base)
    extract = base.lower().endswith((".tar", ".tar.gz", ".tgz")) and not merge_only
    result = out
    log("Собираю старый формат «{}»: {} частей".format(base, len(parts)))
    try:
        if extract:
            tar = tarfile.open(fileobj=reader, mode="r|*", bufsize=CHUNK)
            directories = []
            for member in tar:
                extract_foreign_member(tar, member, out, "overwrite", directories, cancel)
            tar.close()
            for entry in sorted(directories, key=lambda e: len(e["path"].split("/")), reverse=True):
                apply_file_attributes(safe_target(out, entry["path"], False), entry["mode"], entry["mtime"])
            while reader.read(CHUNK):
                pass
        else:
            result = out / base
            if os.path.lexists(str(result)):
                raise ValueError("Файл уже существует: {}".format(result))
            if shutil.disk_usage(str(out)).free < reader.total:
                raise OSError("Не хватает места для склейки")
            try:
                with open(str(result), "wb") as f:
                    while True:
                        data = reader.read(CHUNK)
                        if not data:
                            break
                        f.write(data)
            except BaseException:
                try:
                    result.unlink()
                except OSError:
                    pass
                raise
        actual = reader.sha256.hexdigest()
        if expected is None:
            log("ВНИМАНИЕ: рядом нет {}.sha256".format(base))
        elif actual != expected:
            raise IntegrityError("Контрольная сумма старого набора не совпала: {}".format(base))
        else:
            log("Контрольная сумма совпала")
        return result
    finally:
        reader.close()


def join_files(path, out_dir=None, merge_only=False, log=print, progress=None, cancel=None):
    results = []
    for base, parts in find_legacy_groups(path, log):
        target = Path(os.path.abspath(str(out_dir))) if out_dir else parts[0].parent / "restored"
        results.append(join_legacy_one(base, parts, target, merge_only, log, progress, cancel))
    return results


def join_dispatch(inputs, out_dir=None, on_exist="skip", keep_partial=True, merge_only=False,
                  log=print, progress=None, cancel=None):
    has_legacy_file = any(Path(str(p)).is_file() and PART_RE.match(Path(str(p)).name) for p in inputs)
    has_new_file = any(Path(str(p)).is_file() and Path(str(p)).suffix.lower() == ".tar" for p in inputs)
    if has_legacy_file and not has_new_file:
        results = []
        for path in inputs:
            results.extend(join_files(path, out_dir, merge_only, log, progress, cancel))
        return results
    folders = [Path(str(p)) for p in inputs if Path(str(p)).is_dir()]
    legacy_in_folders = False
    for folder in folders:
        if any(PART_RE.match(p.name) and p.is_file() for p in folder.iterdir()):
            legacy_in_folders = True
    if legacy_in_folders and not has_new_file:
        new_tar_exists = any(any(p.is_file() and p.suffix.lower() == ".tar" for p in folder.iterdir()) for folder in folders)
        if not new_tar_exists:
            results = []
            for folder in folders:
                results.extend(join_files(folder, out_dir, merge_only, log, progress, cancel))
            return results
    return restore_archives(inputs, out_dir, on_exist, keep_partial, log, progress, cancel)


class ConsoleProgress:
    def __init__(self):
        self.last = 0.0

    def __call__(self, done, total):
        now = time.time()
        if done < total and now - self.last < 0.2:
            return
        self.last = now
        pct = 100.0 * done / total if total else 100.0
        sys.stdout.write("\r  {:5.1f}%  {} / {}   ".format(pct, human(done), human(total)))
        sys.stdout.flush()

    def log(self, msg):
        print(msg)


def open_folder(path):
    try:
        if sys.platform.startswith("win"):
            os.startfile(str(path))
        elif sys.platform == "darwin":
            subprocess.Popen(["open", str(path)])
        else:
            subprocess.Popen(["xdg-open", str(path)])
    except Exception:
        pass


def gui_plan_summary(plan):
    done = sum(a["status"] == "done" for a in plan["archives"])
    remaining = sum(a["size"] for a in plan["archives"] if a["status"] != "done")
    return "Готово {} из {}, осталось примерно {}".format(done, len(plan["archives"]), human(remaining))


def run_gui():
    try:
        import tkinter as tk
        from tkinter import filedialog, messagebox, ttk
    except ImportError:
        sys.exit("Не найден tkinter. Консольный режим: python tgsplit.py --help")
    import queue
    if sys.platform.startswith("win"):
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    dnd = None
    try:
        from tkinterdnd2 import DND_FILES, TkinterDnD
        root = TkinterDnD.Tk()
        dnd = DND_FILES
    except Exception:
        root = tk.Tk()
    root.title("TG Splitter — архивы для Telegram")
    root.minsize(760, 700)
    events = queue.Queue()
    cancel = threading.Event()
    state = {"running": False, "out": None, "locked": False}

    notebook = ttk.Notebook(root)
    notebook.pack(fill="x", padx=10, pady=(10, 4))
    split_tab = ttk.Frame(notebook, padding=10)
    join_tab = ttk.Frame(notebook, padding=10)
    notebook.add(split_tab, text="  Разбить  ")
    notebook.add(join_tab, text="  Восстановить  ")

    ttk.Label(split_tab, text="Файлы и папки (можно перетаскивать при установленном tkinterdnd2):").pack(anchor="w")
    source_frame = ttk.Frame(split_tab)
    source_frame.pack(fill="x", pady=4)
    source_list = tk.Listbox(source_frame, height=6, selectmode="extended", activestyle="none")
    source_scroll = ttk.Scrollbar(source_frame, command=source_list.yview)
    source_list.configure(yscrollcommand=source_scroll.set)
    source_list.pack(side="left", fill="x", expand=True)
    source_scroll.pack(side="right", fill="y")
    sources = []

    def add_sources(paths):
        if state["locked"]:
            return
        for path in paths:
            path = os.path.abspath(path)
            if path not in sources:
                sources.append(path)
                source_list.insert("end", path)

    def remove_sources():
        for index in reversed(source_list.curselection()):
            source_list.delete(index)
            del sources[index]

    def clear_sources():
        sources.clear()
        source_list.delete(0, "end")

    source_buttons = ttk.Frame(split_tab)
    source_buttons.pack(fill="x", pady=(0, 6))
    add_file_button = ttk.Button(source_buttons, text="Добавить файлы…",
                                 command=lambda: add_sources(filedialog.askopenfilenames()))
    add_file_button.pack(side="left")

    def add_folder():
        folder = filedialog.askdirectory()
        if folder:
            add_sources([folder])

    add_dir_button = ttk.Button(source_buttons, text="Добавить папку…", command=add_folder)
    add_dir_button.pack(side="left", padx=6)
    remove_button = ttk.Button(source_buttons, text="Убрать выбранное", command=remove_sources)
    remove_button.pack(side="left")
    clear_button = ttk.Button(source_buttons, text="Очистить", command=clear_sources)
    clear_button.pack(side="left", padx=6)

    form = ttk.Frame(split_tab)
    form.pack(fill="x")
    form.columnconfigure(1, weight=1)
    out_split = tk.StringVar()
    name_split = tk.StringVar()
    size_split = tk.StringVar(value="1900M")
    max_parts = tk.StringVar()
    plan_status = tk.StringVar(value="План ещё не выбран")

    def pick_dir(variable):
        folder = filedialog.askdirectory()
        if folder:
            variable.set(folder)

    ttk.Label(form, text="Папка результата:").grid(row=0, column=0, sticky="w", pady=3)
    out_entry = ttk.Entry(form, textvariable=out_split)
    out_entry.grid(row=0, column=1, sticky="ew", padx=6)
    ttk.Button(form, text="Обзор…", command=lambda: pick_dir(out_split)).grid(row=0, column=2)
    ttk.Label(form, text="Имя NAME:").grid(row=1, column=0, sticky="w", pady=3)
    name_entry = ttk.Entry(form, textvariable=name_split)
    name_entry.grid(row=1, column=1, sticky="ew", padx=6)
    ttk.Label(form, text="Размер архива:").grid(row=2, column=0, sticky="w", pady=3)
    size_entry = ttk.Combobox(form, textvariable=size_split, values=("1900M", "3900M"), width=12)
    size_entry.grid(row=2, column=1, sticky="w", padx=6)
    ttk.Label(form, text="Сколько архивов создать сейчас:").grid(row=3, column=0, sticky="w", pady=3)
    ttk.Entry(form, textvariable=max_parts, width=12).grid(row=3, column=1, sticky="w", padx=6)
    ttk.Label(form, text="пусто — все ожидающие", foreground="gray").grid(row=3, column=2, sticky="w")
    ttk.Label(form, textvariable=plan_status, foreground="gray").grid(row=4, column=0, columnspan=3, sticky="w", pady=4)

    ttk.Label(join_tab, text="Архивы .tar (можно несколько и в любом порядке), папка или старые .tar.001:").pack(anchor="w")
    join_frame = ttk.Frame(join_tab)
    join_frame.pack(fill="x", pady=4)
    join_list = tk.Listbox(join_frame, height=6, activestyle="none")
    join_scroll = ttk.Scrollbar(join_frame, command=join_list.yview)
    join_list.configure(yscrollcommand=join_scroll.set)
    join_list.pack(side="left", fill="x", expand=True)
    join_scroll.pack(side="right", fill="y")
    join_sources = []

    def add_join(paths):
        for path in paths:
            path = os.path.abspath(path)
            if path not in join_sources:
                join_sources.append(path)
                join_list.insert("end", path)

    join_buttons = ttk.Frame(join_tab)
    join_buttons.pack(fill="x")
    ttk.Button(join_buttons, text="Добавить архивы…",
               command=lambda: add_join(filedialog.askopenfilenames())).pack(side="left")

    def add_join_folder():
        folder = filedialog.askdirectory()
        if folder:
            add_join([folder])

    ttk.Button(join_buttons, text="Добавить папку…", command=add_join_folder).pack(side="left", padx=6)
    ttk.Button(join_buttons, text="Очистить", command=lambda: (join_sources.clear(), join_list.delete(0, "end"))).pack(side="left")
    join_form = ttk.Frame(join_tab)
    join_form.pack(fill="x", pady=6)
    join_form.columnconfigure(1, weight=1)
    out_join = tk.StringVar()
    on_exist = tk.StringVar(value="skip")
    ttk.Label(join_form, text="Куда восстановить:").grid(row=0, column=0, sticky="w", pady=3)
    ttk.Entry(join_form, textvariable=out_join).grid(row=0, column=1, sticky="ew", padx=6)
    ttk.Button(join_form, text="Обзор…", command=lambda: pick_dir(out_join)).grid(row=0, column=2)
    ttk.Label(join_form, text="Если файл существует:").grid(row=1, column=0, sticky="w", pady=3)
    ttk.Combobox(join_form, textvariable=on_exist, values=("skip", "overwrite", "rename"),
                 state="readonly", width=12).grid(row=1, column=1, sticky="w", padx=6)
    ttk.Label(join_tab, text="Неполные файлы .tgspart сохраняются: можно продолжить с любым следующим окном архивов.",
              foreground="gray", wraplength=680).pack(anchor="w")

    bottom = ttk.Frame(root, padding=(10, 0))
    bottom.pack(fill="both", expand=True)
    controls = ttk.Frame(bottom)
    controls.pack(fill="x", pady=(6, 2))
    controls2 = ttk.Frame(bottom)
    controls2.pack(fill="x", pady=(0, 4))
    run_button = ttk.Button(controls, text="Разбить")
    show_plan_button = ttk.Button(controls, text="Показать план")
    save_plan_button = ttk.Button(controls, text="Сохранить план")
    extend_button = ttk.Button(controls2, text="Обновить план", state="disabled")
    add_to_plan_button = ttk.Button(controls2, text="Добавить папку…", state="disabled")
    cancel_button = ttk.Button(controls, text="Отмена", state="disabled", command=cancel.set)
    open_button = ttk.Button(controls, text="Открыть папку результата", state="disabled",
                             command=lambda: open_folder(state["out"]))
    run_button.pack(side="left")
    show_plan_button.pack(side="left", padx=6)
    save_plan_button.pack(side="left")
    cancel_button.pack(side="left", padx=6)
    extend_button.pack(side="left")
    add_to_plan_button.pack(side="left", padx=6)
    open_button.pack(side="right")
    progress_bar = ttk.Progressbar(bottom, maximum=1000)
    progress_bar.pack(fill="x")
    status_text = tk.StringVar(value="Готов к работе")
    ttk.Label(bottom, textvariable=status_text).pack(anchor="w")
    log_frame = ttk.Frame(bottom)
    log_frame.pack(fill="both", expand=True, pady=(4, 10))
    log_text = tk.Text(log_frame, height=12, state="disabled", wrap="word")
    log_scroll = ttk.Scrollbar(log_frame, command=log_text.yview)
    log_text.configure(yscrollcommand=log_scroll.set)
    log_text.pack(side="left", fill="both", expand=True)
    log_scroll.pack(side="right", fill="y")

    def add_log(message):
        log_text.configure(state="normal")
        log_text.insert("end", str(message) + "\n")
        log_text.see("end")
        log_text.configure(state="disabled")

    def log(message):
        events.put(("log", message))

    last_progress = [0.0]

    def progress(done, total):
        now = time.time()
        if done >= total or now - last_progress[0] > 0.1:
            last_progress[0] = now
            events.put(("progress", done, total))

    def refresh_plan(*_):
        folder = out_split.get().strip()
        try:
            plan = load_plan(folder, name_split.get().strip() or None) if folder else None
        except (ValueError, OSError):
            plan = None
        if plan is not None:
            if not state["locked"]:
                sources[:] = [s["path"] for s in plan["sources"]]
                source_list.delete(0, "end")
                for source in sources:
                    source_list.insert("end", source)
            state["locked"] = True
            extend_button.configure(state="normal" if not state["running"] else "disabled")
            add_to_plan_button.configure(state="normal" if not state["running"] else "disabled")
            plan_status.set(gui_plan_summary(plan))
            source_list.configure(state="disabled")
            for button in (add_file_button, add_dir_button, remove_button, clear_button):
                button.configure(state="disabled")
            name_entry.configure(state="disabled")
            size_entry.configure(state="disabled")
            name_split.set(plan["name"])
            size_split.set(str(plan["parameters"]["part_size"]))
            if notebook.index("current") == 0:
                run_button.configure(text="Продолжить")
        elif not state["running"]:
            state["locked"] = False
            extend_button.configure(state="disabled")
            add_to_plan_button.configure(state="disabled")
            plan_status.set("План ещё не выбран")
            source_list.configure(state="normal")
            for button in (add_file_button, add_dir_button, remove_button, clear_button):
                button.configure(state="normal")
            name_entry.configure(state="normal")
            size_entry.configure(state="normal")
            if notebook.index("current") == 0:
                run_button.configure(text="Разбить")

    out_split.trace_add("write", refresh_plan)

    def show_plan():
        folder = out_split.get().strip()
        try:
            if folder and list(Path(folder).glob("*.plan.json")):
                print_plan(load_plan(folder, name_split.get().strip() or None), add_log)
            elif sources:
                plan = make_plan(sources, folder or Path(sources[0]).parent, parse_size(size_split.get()),
                                 name_split.get().strip() or None, add_log)
                print_plan(plan, add_log)
            else:
                messagebox.showwarning("Нет плана", "Добавьте источники или выберите папку с существующим планом.")
        except Exception as e:
            messagebox.showerror("План", str(e))

    show_plan_button.configure(command=show_plan)

    def start(job):
        if state["running"]:
            return
        state.update(running=True, out=None)
        cancel.clear()
        run_button.configure(state="disabled")
        show_plan_button.configure(state="disabled")
        save_plan_button.configure(state="disabled")
        extend_button.configure(state="disabled")
        add_to_plan_button.configure(state="disabled")
        cancel_button.configure(state="normal")
        open_button.configure(state="disabled")
        progress_bar["value"] = 0
        log_text.configure(state="normal")
        log_text.delete("1.0", "end")
        log_text.configure(state="disabled")
        status_text.set("Работаю…")

        def target():
            try:
                result = job()
                events.put(("done", True, result))
            except Cancelled:
                events.put(("done", False, "Отменено; готовые архивы и план сохранены"))
            except Exception as e:
                events.put(("done", False, str(e) or e.__class__.__name__))

        threading.Thread(target=target, daemon=True).start()

    def do_split():
        if not sources:
            messagebox.showwarning("Нечего разбивать", "Добавьте файлы или папку.")
            return
        try:
            size = parse_size(size_split.get())
            count_text = max_parts.get().strip()
            count = int(count_text) if count_text else None
            if count is not None and count < 1:
                raise ValueError("Число архивов должно быть положительным")
            name = name_split.get().strip() or None
            folder = out_split.get().strip()
            if not folder:
                base = name or (Path(sources[0]).name if len(sources) == 1 else "archive")
                folder = str(Path(sources[0]).parent / (base + "_parts"))
                out_split.set(folder)
            locked = state["locked"]

            def job():
                plan = split_plan([] if locked else list(sources), folder, size, name, count,
                                  log=log, progress=progress, cancel=cancel,
                                  hash_progress=progress)
                state["out"] = folder
                return gui_plan_summary(plan)

            start(job)
        except ValueError as e:
            messagebox.showerror("Разбивка", str(e))

    def do_extend():
        folder = out_split.get().strip()
        if not folder or not state["locked"]:
            messagebox.showwarning("Нет плана", "Сначала выберите папку с существующим планом.")
            return
        try:
            def job():
                plan = extend_plan(folder, name_split.get().strip() or None, None, True,
                                   log=log, progress=progress, cancel=cancel)
                state["out"] = folder
                return "План обновлён; архивы создаст «Продолжить». " + gui_plan_summary(plan)

            start(job)
        except ValueError as e:
            messagebox.showerror("Обновление плана", str(e))

    extend_button.configure(command=do_extend)

    def do_add_to_plan():
        folder = out_split.get().strip()
        if not folder or not state["locked"]:
            messagebox.showwarning("Нет плана", "Сначала выберите папку с существующим планом.")
            return
        new_dir = filedialog.askdirectory(title="Новая папка для добавления в план")
        if not new_dir:
            return
        try:
            def job():
                plan = extend_plan(folder, name_split.get().strip() or None, None, True,
                                   log=log, progress=progress, cancel=cancel, add_paths=[new_dir])
                state["out"] = folder
                return "Папка добавлена в план; архивы создаст «Продолжить». " + gui_plan_summary(plan)

            start(job)
        except ValueError as e:
            messagebox.showerror("Добавление папки", str(e))

    add_to_plan_button.configure(command=do_add_to_plan)

    def do_save_plan():
        if not sources:
            messagebox.showwarning("Нечего сохранять", "Добавьте файлы или папку.")
            return
        try:
            size = parse_size(size_split.get())
            name = name_split.get().strip() or None
            folder = out_split.get().strip()
            if not folder:
                base = name or (Path(sources[0]).name if len(sources) == 1 else "archive")
                folder = str(Path(sources[0]).parent / (base + "_parts"))
                out_split.set(folder)

            def job():
                plan = save_plan_only(list(sources), folder, size, name, log, progress, cancel)
                state["out"] = folder
                return "План сохранён. " + gui_plan_summary(plan)

            start(job)
        except ValueError as e:
            messagebox.showerror("План", str(e))

    save_plan_button.configure(command=do_save_plan)

    def do_join():
        if not join_sources:
            messagebox.showwarning("Нечего восстанавливать", "Добавьте архивы или папку.")
            return

        def job():
            result = join_dispatch(list(join_sources), out_join.get().strip() or None, on_exist.get(),
                                   True, False, log, progress, cancel)
            state["out"] = out_join.get().strip() or str(Path(join_sources[0]).parent / "restored")
            if isinstance(result, dict):
                return "Восстановление завершено: {} полных, {} неполных".format(
                    len(result["complete"]), len(result["incomplete"]))
            return "Старые части собраны: {}".format(len(result))

        start(job)

    def on_tab(_=None):
        split_active = notebook.index("current") == 0
        run_button.configure(text="Продолжить" if split_active and state["locked"] else
                             ("Разбить" if split_active else "Восстановить"),
                             command=do_split if split_active else do_join)
        if split_active:
            show_plan_button.configure(state="normal" if not state["running"] else "disabled")
            save_plan_button.configure(state="normal" if not state["running"] and not state["locked"] else "disabled")
            extend_button.configure(state="normal" if state["locked"] and not state["running"] else "disabled")
            add_to_plan_button.configure(state="normal" if state["locked"] and not state["running"] else "disabled")
        else:
            show_plan_button.configure(state="disabled")
            save_plan_button.configure(state="disabled")
            extend_button.configure(state="disabled")
            add_to_plan_button.configure(state="disabled")

    notebook.bind("<<NotebookTabChanged>>", on_tab)
    if dnd:
        source_list.drop_target_register(dnd)
        source_list.dnd_bind("<<Drop>>", lambda e: add_sources(root.tk.splitlist(e.data)))
        join_list.drop_target_register(dnd)
        join_list.dnd_bind("<<Drop>>", lambda e: add_join(root.tk.splitlist(e.data)))

    def poll():
        try:
            while True:
                event = events.get_nowait()
                if event[0] == "log":
                    add_log(event[1])
                elif event[0] == "progress":
                    _, done, total = event
                    progress_bar["value"] = 1000.0 * done / total if total else 1000
                    status_text.set("{} / {}".format(human(done), human(total)))
                elif event[0] == "done":
                    _, ok, message = event
                    state["running"] = False
                    run_button.configure(state="normal")
                    cancel_button.configure(state="disabled")
                    if state["out"]:
                        open_button.configure(state="normal")
                    status_text.set(message)
                    add_log(message)
                    refresh_plan()
                    on_tab()
                    if not ok and not str(message).startswith("Отменено"):
                        messagebox.showerror("Ошибка", message)
        except queue.Empty:
            pass
        root.after(100, poll)

    on_tab()
    poll()
    root.mainloop()
    return 0


class RussianArgumentParser(argparse.ArgumentParser):
    def __init__(self, *args, **kwargs):
        kwargs["add_help"] = False
        kwargs.setdefault("formatter_class", argparse.RawDescriptionHelpFormatter)
        super().__init__(*args, **kwargs)
        self._positionals.title = "Позиционные аргументы"
        self._optionals.title = "Параметры"
        self.add_argument("-h", "--help", action="help", help="показать эту справку и выйти")

    def format_help(self):
        return super().format_help().replace("usage:", "Использование:", 1)

    def format_usage(self):
        return super().format_usage().replace("usage:", "Использование:", 1)


def build_parser():
    ap = RussianArgumentParser(
        prog="tgsplit",
        description="Независимые несжатые TAR-архивы до 2 ГБ с продолжением и восстановлением любых окон.",
        epilog="""plan сохраняет план, но не создаёт архивы. split без PATHS продолжает план;
готовые архивы и источники для них уже не нужны. --only выбирает ожидающие,
--redo пересоздаёт готовые. extend добавляет новые и перенесённые файлы в конец
набора, не меняя старые архивы. plan.json — главный файл состояния, не удаляйте его.
При аварийном завершении останется NAME.lock: удалите его только убедившись,
что другой процесс не работает. Восстановление принимает любые архивы в любом
порядке и сохраняет неполные .tgspart в .tgsplit-restore.json.
Сохраняются пути, режимы, mtime (секунды), ссылки и пустые папки; ACL, xattr,
атрибуты Windows, uid/gid и жёсткие связи не сохраняются. Старые name.tar.001
поддерживаются join. Без аргументов открывается окно.""",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    for command, help_text in (("plan", "только построить и сохранить план"),
                               ("split", "создать или продолжить архивы")):
        s = sub.add_parser(command, help=help_text)
        s.add_argument("paths", nargs="*" if command == "split" else "+", help="файлы и/или папки")
        s.add_argument("-o", "--output", required=True, help="папка результата")
        s.add_argument("-s", "--size", default="{}M".format(DEFAULT_PART_MB),
                       help="ёмкость архива, минимум 64 КиБ; по умолчанию 1900M (МиБ)")
        s.add_argument("-n", "--name", help="базовое имя NAME")
        if command == "split":
            s.add_argument("--max-parts", type=int, help="создать не больше N первых ожидающих архивов")
            s.add_argument("--only", help="создать конкретные ожидающие архивы, например 6,7")
            s.add_argument("--redo", help="пересоздать готовые архивы, например 3")
    ex = sub.add_parser("extend", help="добавить новые и перенесённые файлы в новые архивы")
    ex.add_argument("-o", "--output", required=True, help="папка с существующим планом")
    ex.add_argument("-n", "--name", help="базовое имя NAME, если планов несколько")
    ex.add_argument("--max-parts", type=int, help="создать не больше N новых архивов")
    ex.add_argument("--plan-only", action="store_true", help="только расширить план, не создавать архивы")
    ex.add_argument("--add", action="append", metavar="ПУТЬ", default=[],
                    help="добавить новую корневую папку или файл в существующий план (можно несколько раз)")
    st = sub.add_parser("status", help="показать состояние плана")
    st.add_argument("output", help="папка OUT или файл plan.json")
    st.add_argument("-n", "--name", help="базовое имя NAME, если планов несколько")
    vf = sub.add_parser("verify", help="проверить присутствующие архивы по .sha256")
    vf.add_argument("output", help="папка OUT или файл plan.json")
    vf.add_argument("-n", "--name", help="базовое имя NAME, если планов несколько")
    j = sub.add_parser("join", help="восстановить любые архивы/окна или старые части .tar.001")
    j.add_argument("paths", nargs="+", help="архивы TAR, папка или старая часть name.tar.001")
    j.add_argument("-o", "--output", help="папка восстановления (по умолчанию restored)")
    j.add_argument("--on-exist", choices=("skip", "overwrite", "rename"), default="skip",
                   help="что делать с существующими файлами (по умолчанию skip)")
    j.add_argument("--discard-partial", action="store_true",
                   help="удалить неполные .tgspart после отчёта (по умолчанию сохранять для продолжения)")
    j.add_argument("--merge-only", action="store_true", help="старый формат: только склеить, не распаковывать")
    sub.add_parser("gui", help="открыть графическое окно")
    return ap


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if not argv:
        return run_gui()
    args = build_parser().parse_args(argv)
    cp = ConsoleProgress()
    try:
        if args.cmd == "gui":
            return run_gui()
        if args.cmd == "status":
            print_status(load_plan(args.output, args.name), cp.log)
        elif args.cmd == "verify":
            verify_archives(args.output, args.name, cp.log)
        elif args.cmd == "join":
            join_dispatch(args.paths, args.output, args.on_exist, not args.discard_partial,
                          args.merge_only, cp.log, cp)
        elif args.cmd == "plan":
            save_plan_only(args.paths, args.output, parse_size(args.size), args.name, cp.log, cp)
        elif args.cmd == "extend":
            extend_plan(args.output, args.name, args.max_parts, args.plan_only, cp.log, cp,
                        add_paths=args.add or None)
        else:
            split_plan(args.paths, args.output, parse_size(args.size), args.name,
                       args.max_parts, args.only, args.redo, cp.log, cp)
        return 0
    except (KeyboardInterrupt, Cancelled):
        cp.log("Отменено")
        return 130
    except IntegrityError as e:
        cp.log("ОШИБКА ЦЕЛОСТНОСТИ: {}".format(e))
        return 2
    except tarfile.TarError as e:
        cp.log("ОШИБКА{}: {}".format(" ЦЕЛОСТНОСТИ" if args.cmd == "join" else "", e))
        return 2 if args.cmd == "join" else 1
    except (ValueError, OSError) as e:
        cp.log("ОШИБКА: {}".format(e))
        return 1


if __name__ == "__main__":
    sys.exit(main())