# -*- coding: utf-8 -*-
import hashlib
import io
import json
import os
import random
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest
from pathlib import Path

import tgsplit as tg


class TempCase(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="tgsplit-test-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)

    def tree(self, name="src"):
        p = self.tmp / name
        p.mkdir()
        return p

    def plan(self, src, size=300 * 1024, name="data"):
        out = self.tmp / (name + "-out")
        out.mkdir(exist_ok=True)
        return tg.make_plan([src], out, size, name, log=lambda s: None)


def assert_layout(case, plan, capacity):
    positions = {f["path"]: 0 for f in plan["files"] if f["type"] == "file"}
    expected_order = [f["path"] for f in plan["files"]]
    actual_order = []
    seen_fragments = {}
    case.assertEqual([a["index"] for a in plan["archives"]], list(range(1, len(plan["archives"]) + 1)))
    for archive in plan["archives"]:
        case.assertLessEqual(archive["size"], capacity)
        case.assertEqual(archive["size"], tg.archive_estimate(plan, archive))
        for entry in archive["entries"]:
            logical = entry.get("source_path", entry["path"])
            actual_order.append(logical)
            frag = entry.get("fragment")
            if not frag:
                if logical in positions:
                    case.assertEqual(positions[logical], 0)
                    positions[logical] += entry["size"]
                continue
            key = logical
            seen_fragments.setdefault(key, []).append(frag)
            case.assertEqual(frag["offset"], positions[logical])
            case.assertEqual(frag["length"], entry["size"])
            case.assertEqual(frag["total_size"], next(f["size"] for f in plan["files"] if f["path"] == logical))
            positions[logical] += entry["size"]
            if positions[logical] < frag["total_size"]:
                case.assertEqual(entry["size"] % 512, 0)
    compact_order = []
    for p in actual_order:
        if not compact_order or compact_order[-1] != p:
            compact_order.append(p)
    case.assertEqual(compact_order, [p for p in expected_order if any(
        e.get("source_path", e["path"]) == p for a in plan["archives"] for e in a["entries"])])
    for logical, frags in seen_fragments.items():
        case.assertEqual([f["index"] for f in frags], list(range(1, len(frags) + 1)))
        case.assertTrue(all(f["count"] == len(frags) for f in frags))
    for f in plan["files"]:
        if f["type"] == "file":
            case.assertEqual(positions[f["path"]], f["size"])


class PlannerTests(TempCase):
    def test_random_unicode_long_empty_symlink_and_zero(self):
        rng = random.Random(712367)
        for iteration in range(20):
            with self.subTest(iteration=iteration):
                root = self.tmp / "random-{}".format(iteration)
                root.mkdir()
                (root / "empty").mkdir()
                (root / "zero").write_bytes(b"")
                (root / "кириллица-😀").write_bytes(os.urandom(rng.randrange(0, 5000)))
                long_dir = root / ("д" * 70)
                long_dir.mkdir()
                (long_dir / ("ф" * 80)).write_bytes(os.urandom(rng.randrange(0, 10000)))
                for i in range(15):
                    p = root / "dir{}".format(i % 3) / "file-{:02d}".format(i)
                    p.parent.mkdir(exist_ok=True)
                    p.write_bytes(os.urandom(rng.randrange(0, 100000)))
                    os.utime(str(p), ns=(1_500_000_000_000_000_000 + i, 1_500_000_000_000_000_000 + i))
                if hasattr(os, "symlink"):
                    try:
                        os.symlink("zero", str(root / "link"))
                    except (OSError, NotImplementedError):
                        pass
                plan = self.plan(root)
                assert_layout(self, plan, 300 * 1024)
                paths = {f["path"] for f in plan["files"]}
                self.assertIn("random-{}".format(iteration) + "/empty", paths)

    def test_boundaries_around_fragment_capacity(self):
        root = self.tree("boundary")
        probe = root / "probe"
        probe.write_bytes(b"x")
        base = self.plan(root)
        logical = {"path": "x", "type": "file", "size": 1, "mode": 0o644, "mtime": 0}
        cap = tg._max_fragment(base, logical, 300 * 1024)
        shutil.rmtree(root)
        root.mkdir()
        sizes = [cap - 10240, cap - 1024, cap - 513, cap - 512, cap - 1,
                 cap, cap + 1, cap + 511, cap + 512, cap + 513, cap + 10240]
        for i, size in enumerate(sizes):
            (root / "{:02d}".format(i)).write_bytes(b"\0" * max(0, size))
        plan = self.plan(root, name="bounds")
        assert_layout(self, plan, 300 * 1024)
        for f in plan["files"]:
            fragments = [e for a in plan["archives"] for e in a["entries"]
                         if e.get("source_path") == f["path"]]
            if f["size"] <= cap:
                self.assertLessEqual(len(fragments), 1, (f["path"], f["size"], cap))
            else:
                self.assertGreaterEqual(len(fragments), 2, f["path"])

    def test_duplicate_names_nested_sources_and_plan_cli(self):
        a = self.tmp / "a" / "Photos"
        b = self.tmp / "b" / "Photos"
        a.mkdir(parents=True)
        b.mkdir(parents=True)
        (a / "a").write_text("a")
        (b / "b").write_text("b")
        plan = tg.make_plan([a, b], self.tmp, 300 * 1024, "x", log=lambda s: None)
        self.assertEqual([s["name"] for s in plan["sources"]], ["Photos", "Photos_2"])
        with self.assertRaisesRegex(ValueError, "Вложенные"):
            tg.make_plan([a.parent, a], self.tmp, 300 * 1024, "bad", log=lambda s: None)
        out = self.tmp / "cli"
        code = tg.main(["plan", str(a), "-o", str(out), "-s", "300K", "-n", "dry"])
        self.assertEqual(code, 0)
        self.assertTrue((out / "dry.plan.json").is_file())
        self.assertEqual(list(out.glob("*.tar")), [])

    def test_hard_link_planned_as_two_regular_files(self):
        root = self.tree("hard")
        (root / "a").write_bytes(b"same")
        try:
            os.link(str(root / "a"), str(root / "b"))
        except OSError:
            self.skipTest("hard links are unavailable")
        plan = self.plan(root)
        entries = [f for f in plan["files"] if f["type"] == "file"]
        self.assertEqual(len(entries), 2)
        self.assertTrue(all(e["type"] == "file" for e in entries))


class ArchiveBuildTests(TempCase):
    def make_big_tree(self):
        root = self.tree("build")
        (root / "empty").mkdir()
        (root / "a").write_bytes(os.urandom(180 * 1024))
        (root / "b").write_bytes(os.urandom(400 * 1024))
        (root / "ю").write_bytes(b"unicode")
        os.utime(str(root / "a"), (1_600_000_000, 1_600_000_000))
        return root

    def test_size_limits_tar_structure_and_sidecars(self):
        root = self.make_big_tree()
        plan = self.plan(root, name="sizes")
        out = self.tmp / "sizes-out"
        estimates = [a["size"] for a in plan["archives"]]
        for i, archive in enumerate(plan["archives"], 1):
            target = tg.build_archive(plan, out, i, log=lambda s: None)
            actual = target.stat().st_size
            self.assertLessEqual(actual, 300 * 1024)
            self.assertLessEqual(actual, estimates[i - 1])
            self.assertEqual(actual % 10240, 0)
            digest = hashlib.sha256(target.read_bytes()).hexdigest()
            self.assertEqual(digest, archive["sha256"])
            self.assertEqual(Path(str(target) + ".sha256").read_text().split()[0], digest)
            with tarfile.open(str(target), "r:") as tar:
                members = tar.getmembers()
                self.assertEqual(members[0].name, ".tgsplit/manifest.json")
                self.assertEqual(members[-1].name, ".tgsplit/entries.sha256")
                manifest = json.load(tar.extractfile(members[0]))
                self.assertEqual(manifest["plan_id"], plan["plan_id"])
                self.assertEqual(manifest["archive"], i)
                self.assertEqual(manifest["total_archives"], len(plan["archives"]))

    def test_determinism_and_preflight(self):
        root = self.make_big_tree()
        out1 = self.tmp / "one"
        out2 = self.tmp / "two"
        p1 = tg.make_plan([root], out1, 300 * 1024, "same", log=lambda s: None)
        p2 = tg.make_plan([root], out2, 300 * 1024, "same", log=lambda s: None)
        self.assertEqual(p1["plan_id"], p2["plan_id"])
        for i in range(1, len(p1["archives"]) + 1):
            a = tg.build_archive(p1, out1, i, log=lambda s: None)
            b = tg.build_archive(p2, out2, i, log=lambda s: None)
            self.assertEqual(hashlib.sha256(a.read_bytes()).hexdigest(),
                             hashlib.sha256(b.read_bytes()).hexdigest())
        victim = self.tmp / "changed"
        victim.mkdir()
        f = victim / "f"
        f.write_bytes(b"before")
        p3 = tg.make_plan([victim], self.tmp, 300 * 1024, "changed", log=lambda s: None)
        f.write_bytes(b"after!")
        with self.assertRaises(tg.IntegrityError):
            tg.build_archive(p3, victim.parent / "changed-out", 1, log=lambda s: None)
        self.assertEqual(list((victim.parent / "changed-out").glob("*.part")), [])


class ResumeTests(TempCase):
    def make_resume_plan(self):
        root = self.tree("resume")
        for name, size in (("a", 180 * 1024), ("b", 280 * 1024), ("c", 510 * 1024),
                           ("d", 33 * 1024)):
            (root / name).write_bytes(os.urandom(size))
        out = self.tmp / "resume-out"
        plan = tg.make_plan([root], out, 300 * 1024, "resume", log=lambda s: None)
        self.assertGreaterEqual(len(plan["archives"]), 4)
        return root, out, plan

    def test_max_parts_resume_after_deleting_done_and_only_redo(self):
        root, out, original = self.make_resume_plan()
        first = tg.split_plan([root], out, 300 * 1024, "resume", max_parts=2, log=lambda s: None)
        self.assertEqual([a["status"] for a in first["archives"]].count("done"), 2)
        for i in (1, 2):
            tg.archive_path(out, first, i).unlink()
            Path(str(tg.archive_path(out, first, i)) + ".sha256").unlink()
        selected = tg.split_plan([], out, name="resume", only="4", log=lambda s: None)
        self.assertEqual(selected["archives"][3]["status"], "done")
        old_hash = selected["archives"][3]["sha256"]
        redone = tg.split_plan([], out, name="resume", redo="4", log=lambda s: None)
        self.assertEqual(redone["archives"][3]["sha256"], old_hash)
        final = tg.split_plan([], out, name="resume", log=lambda s: None)
        self.assertTrue(all(a["status"] == "done" for a in final["archives"]))
        self.assertEqual(len(list(out.glob("resume.*.tar"))), len(final["archives"]) - 2)
        tg.split_plan([], out, name="resume", redo="1,2", log=lambda s: None)
        restored = self.tmp / "resume-restored"
        report = tg.restore_archives([out], restored, log=lambda s: None)
        self.assertEqual(report["incomplete"], [])
        for name in ("a", "b", "c", "d"):
            self.assertEqual((restored / "resume" / name).read_bytes(), (root / name).read_bytes())
        self.assertFalse((out / "resume.lock").exists())

    def test_cancel_mid_archive_leaves_no_part_and_resume_works(self):
        root, out, original = self.make_resume_plan()
        calls = []

        def stop(done, total):
            calls.append(done)
            if done:
                raise tg.Cancelled()

        with self.assertRaises(tg.Cancelled):
            tg.split_plan([root], out, 300 * 1024, "resume", log=lambda s: None, progress=stop)
        self.assertTrue(calls)
        self.assertEqual(list(out.glob("*.part")), [])
        saved = tg.load_plan(out)
        self.assertTrue(all(a["status"] == "pending" for a in saved["archives"]))
        result = tg.split_plan([], out, name="resume", log=lambda s: None)
        self.assertTrue(all(a["status"] == "done" for a in result["archives"]))

    def test_modified_done_source_does_not_block_pending(self):
        root, out, plan = self.make_resume_plan()
        tg.split_plan([root], out, 300 * 1024, "resume", max_parts=1, log=lambda s: None)
        first_files = [e for e in plan["archives"][0]["entries"] if e["type"] == "file"]
        self.assertTrue(first_files)
        logical = next(f for f in plan["files"] if f["path"] == first_files[0].get("source_path", first_files[0]["path"]))
        with open(logical["source"], "ab") as f:
            f.write(b"changed")
        result = tg.split_plan([], out, name="resume", log=lambda s: None)
        self.assertTrue(all(a["status"] == "done" for a in result["archives"]))

    def test_lock_status_and_path_mismatch(self):
        root, out, plan = self.make_resume_plan()
        out.mkdir(exist_ok=True)
        lock = out / "resume.lock"
        lock.write_text("other")
        with self.assertRaisesRegex(ValueError, "Другой процесс"):
            tg.split_plan([root], out, 300 * 1024, "resume", log=lambda s: None)
        lock.unlink()
        tg.split_plan([root], out, 300 * 1024, "resume", max_parts=1, log=lambda s: None)
        with self.assertRaisesRegex(ValueError, "не совпадают"):
            tg.split_plan([self.tmp], out, 300 * 1024, "resume", log=lambda s: None)
        self.assertEqual(tg.main(["status", str(out)]), 0)


class MissingFilesTests(TempCase):
    def test_deleted_files_are_skipped_not_fatal(self):
        src = self.tree()
        for i in range(5):
            (src / "f{}.bin".format(i)).write_bytes(os.urandom(200 * 1024))
        out = self.tmp / "out"
        tg.create_plan([src], out, 300 * 1024, "data", log=lambda s: None)
        (src / "f1.bin").unlink()
        (src / "f3.bin").unlink()
        logs = []
        plan = tg.split_plan([], out, log=logs.append)
        self.assertTrue(all(a["status"] == "done" for a in plan["archives"]))
        self.assertTrue(any("нет файла" in line for line in logs))
        restored = self.tmp / "restored"
        tg.restore_archives([out], restored, "skip", True, lambda s: None)
        names = sorted(p.name for p in restored.rglob("*.bin"))
        self.assertEqual(names, ["f0.bin", "f2.bin", "f4.bin"])


class MissingFragmentedFileTests(TempCase):
    def test_large_file_deleted_midway_restores_cleanly_in_any_order(self):
        src = self.tree()
        (src / "big.bin").write_bytes(os.urandom(900 * 1024))
        for i in range(3):
            (src / "p{}.jpg".format(i)).write_bytes(os.urandom(100 * 1024))
        out = self.tmp / "out"
        plan = tg.create_plan([src], out, 300 * 1024, "data", log=lambda s: None)
        self.assertGreater(len(plan["archives"]), 3)
        tg.split_plan([], out, max_parts=2, log=lambda s: None)
        (src / "big.bin").unlink()
        tg.split_plan([], out, log=lambda s: None)
        archives = sorted(out.glob("*.tar"), reverse=True)
        restored = self.tmp / "restored"
        report = tg.restore_archives(archives, restored, "skip", True, lambda s: None)
        self.assertEqual(report["incomplete"], [])
        self.assertEqual(list(restored.rglob("*.tgspart")), [])
        self.assertEqual(sorted(p.name for p in restored.rglob("*.jpg")), ["p0.jpg", "p1.jpg", "p2.jpg"])
        self.assertFalse(list(restored.rglob("big.bin*")))


class AddRootSourceTests(TempCase):
    def test_extend_adds_new_root_folder_and_keeps_plan_id(self):
        y1 = self.tree("y2026")
        (y1 / "a.bin").write_bytes(os.urandom(100 * 1024))
        out = self.tmp / "out"
        plan = tg.create_plan([y1], out, 300 * 1024, "photos", log=lambda s: None)
        tg.split_plan([], out, log=lambda s: None)
        y2 = self.tree("y2027")
        (y2 / "b.bin").write_bytes(os.urandom(100 * 1024))
        sub = y1 / "sub"
        sub.mkdir()
        with self.assertRaises(ValueError):
            tg.extend_plan(out, add_paths=[sub], log=lambda s: None)
        with self.assertRaises(ValueError):
            tg.extend_plan(out, add_paths=[y1], log=lambda s: None)
        after = tg.extend_plan(out, add_paths=[y2], log=lambda s: None)
        self.assertEqual(after["plan_id"], plan["plan_id"])
        self.assertEqual([s["name"] for s in after["sources"]], ["y2026", "y2027"])
        self.assertTrue(all(a["status"] == "done" for a in after["archives"]))
        restored = self.tmp / "restored"
        tg.restore_archives([out], restored, "skip", True, lambda s: None)
        self.assertEqual(sorted(p.name for p in restored.rglob("*.bin")), ["a.bin", "b.bin"])


class RenameGuardTests(TempCase):
    def test_rename_without_update_is_refused_and_update_fixes_it(self):
        src = self.tree()
        (src / "old").mkdir()
        for i in range(3):
            (src / "old" / "f{}.bin".format(i)).write_bytes(os.urandom(200 * 1024 + i))
        out = self.tmp / "out"
        tg.create_plan([src], out, 300 * 1024, "data", log=lambda s: None)
        tg.split_plan([], out, max_parts=1, log=lambda s: None)
        (src / "old").rename(src / "new")
        with self.assertRaises(ValueError):
            tg.split_plan([], out, log=lambda s: None)
        tg.extend_plan(out, plan_only=True, log=lambda s: None)
        tg.split_plan([], out, log=lambda s: None)
        restored = self.tmp / "restored"
        tg.restore_archives([out], restored, "skip", True, lambda s: None)
        names = sorted(str(p.relative_to(restored)).replace(os.sep, "/") for p in restored.rglob("*.bin"))
        self.assertEqual(names, ["src/new/f0.bin", "src/new/f1.bin", "src/new/f2.bin"])


class RestoreTests(TempCase):
    def split_tree(self):
        root = self.tree("restore-src")
        (root / "empty-dir").mkdir()
        (root / "zero").write_bytes(b"")
        contents = {
            "a": os.urandom(170 * 1024),
            "b": os.urandom(410 * 1024 + 17),
            "c": os.urandom(280 * 1024),
            "d": os.urandom(90 * 1024 + 1),
        }
        for name, data in contents.items():
            (root / name).write_bytes(data)
            os.utime(str(root / name), (1_610_000_000 + len(name), 1_610_000_000 + len(name)))
        os.utime(str(root / "empty-dir"), (1_600_000_123, 1_600_000_123))
        try:
            os.symlink("zero", str(root / "symbolic-link"))
        except (OSError, NotImplementedError):
            pass
        out = self.tmp / "restore-archives"
        plan = tg.split_plan([root], out, 300 * 1024, "restore", log=lambda s: None)
        return root, out, plan, contents

    def expected_window(self, plan, first, last):
        selected = [e for a in plan["archives"] if first <= a["index"] <= last for e in a["entries"]]
        complete = set()
        incomplete = set()
        grouped = {}
        for entry in selected:
            if "fragment" in entry:
                grouped.setdefault(entry["source_path"], []).append(entry["fragment"]["index"])
            elif entry["type"] == "file":
                complete.add(entry["path"])
        counts = {e["source_path"]: e["fragment"]["count"] for a in plan["archives"]
                  for e in a["entries"] if "fragment" in e}
        for path, indices in grouped.items():
            if len(indices) == counts[path]:
                complete.add(path)
            else:
                incomplete.add(path)
        return complete, incomplete

    def test_full_cycle_content_mtime_empty_dirs_and_hardlinks(self):
        root, out, plan, contents = self.split_tree()
        hard_a = root / "hard-a"
        hard_b = root / "hard-b"
        hard_a.write_bytes(b"independent")
        try:
            os.link(str(hard_a), str(hard_b))
            out2 = self.tmp / "hard-archives"
            plan2 = tg.split_plan([root], out2, 300 * 1024, "hard", log=lambda s: None)
            restored2 = self.tmp / "hard-restored"
            tg.restore_archives([out2], restored2, log=lambda s: None)
            self.assertEqual((restored2 / "restore-src" / "hard-a").read_bytes(), b"independent")
            self.assertEqual((restored2 / "restore-src" / "hard-b").read_bytes(), b"independent")
            self.assertEqual((restored2 / "restore-src" / "hard-a").stat().st_nlink, 1)
            self.assertEqual((restored2 / "restore-src" / "hard-b").stat().st_nlink, 1)
        except OSError:
            pass
        restored = self.tmp / "full-restored"
        report = tg.restore_archives([out], restored, log=lambda s: None)
        self.assertEqual(report["incomplete"], [])
        for name, data in contents.items():
            target = restored / "restore-src" / name
            self.assertEqual(target.read_bytes(), data)
            self.assertEqual(int(target.stat().st_mtime), int((root / name).stat().st_mtime))
            self.assertEqual(stat.S_IMODE(target.stat().st_mode), stat.S_IMODE((root / name).stat().st_mode))
        if os.path.islink(str(root / "symbolic-link")):
            self.assertEqual(os.readlink(str(restored / "restore-src" / "symbolic-link")), "zero")
        self.assertTrue((restored / "restore-src" / "empty-dir").is_dir())
        self.assertEqual(int((restored / "restore-src" / "empty-dir").stat().st_mtime), 1_600_000_123)
        self.assertEqual((restored / "restore-src" / "zero").read_bytes(), b"")

    def test_every_archive_range_and_multiple_runs(self):
        root, out, plan, contents = self.split_tree()
        archives = [tg.archive_path(out, plan, i) for i in range(1, len(plan["archives"]) + 1)]
        for first in range(1, len(archives) + 1):
            for last in range(first, len(archives) + 1):
                with self.subTest(first=first, last=last):
                    expected_complete, expected_incomplete = self.expected_window(plan, first, last)
                    dest = self.tmp / "window-{}-{}".format(first, last)
                    report = tg.restore_archives(archives[first - 1:last], dest, log=lambda s: None)
                    self.assertEqual(set(report["complete"]), expected_complete)
                    self.assertEqual({x["path"] for x in report["incomplete"]}, expected_incomplete)
                    for logical in expected_complete:
                        relative = logical.split("/", 1)[1]
                        self.assertEqual((dest / logical).read_bytes(), (root / relative).read_bytes())
        first, last = 1, len(archives)
        one = self.tmp / "one-run"
        many = self.tmp / "many-runs"
        tg.restore_archives(archives, one, log=lambda s: None)
        for archive in reversed(archives):
            tg.restore_archives([archive], many, log=lambda s: None)
        for logical in self.expected_window(plan, first, last)[0]:
            self.assertEqual((one / logical).read_bytes(), (many / logical).read_bytes())
        self.assertEqual(tg.restore_archives([archives[-1]], many, log=lambda s: None)["incomplete"], [])
        self.assertEqual(list(many.rglob("*.tgspart")), [])

    def test_verify_and_flipped_byte_exit_two(self):
        root, out, plan, contents = self.split_tree()
        target = tg.archive_path(out, plan, 1)
        self.assertEqual(tg.main(["verify", str(out)]), 0)
        data = bytearray(target.read_bytes())
        data[len(data) // 2] ^= 1
        target.write_bytes(data)
        self.assertEqual(tg.main(["verify", str(out)]), 2)
        self.assertEqual(tg.main(["join", str(target), "-o", str(self.tmp / "bad-restore")]), 2)
        self.assertTrue(target.exists())
        self.assertTrue((out / "restore.plan.json").exists())

    def make_attack_tar(self, name, member_name, linkname=None):
        path = self.tmp / name
        with tarfile.open(str(path), "w", format=tarfile.PAX_FORMAT) as tar:
            info = tarfile.TarInfo(member_name)
            info.mtime = 0
            if linkname is None:
                data = b"attack"
                info.size = len(data)
                tar.addfile(info, io.BytesIO(data))
            else:
                info.type = tarfile.SYMTYPE
                info.linkname = linkname
                tar.addfile(info)
        return path

    def test_path_attacks_and_mixed_plan_ids(self):
        for i, name in enumerate(("../escape", "/absolute", "C:/absolute")):
            path = self.make_attack_tar("attack{}.tar".format(i), name)
            with self.subTest(name=name), self.assertRaises(ValueError):
                tg.restore_archives([path], self.tmp / "attack-out-{}".format(i), log=lambda s: None)
        link = self.make_attack_tar("link.tar", "link", "../outside")
        with self.assertRaises(ValueError):
            tg.restore_archives([link], self.tmp / "link-out", log=lambda s: None)
        one = self.tmp / "one-src"
        two = self.tmp / "two-src"
        one.mkdir()
        two.mkdir()
        (one / "a").write_bytes(b"a")
        (two / "b").write_bytes(b"b")
        tg.split_plan([one], self.tmp / "one-out", 300 * 1024, "one", log=lambda s: None)
        tg.split_plan([two], self.tmp / "two-out", 300 * 1024, "two", log=lambda s: None)
        dest = self.tmp / "mixed"
        tg.restore_archives([self.tmp / "one-out" / "one.0001.tar"], dest, log=lambda s: None)
        with self.assertRaisesRegex(ValueError, "plan_id"):
            tg.restore_archives([self.tmp / "two-out" / "two.0001.tar"], dest, log=lambda s: None)


class LegacyJoinTests(TempCase):
    def make_legacy(self):
        folder = self.tmp / "legacy"
        folder.mkdir()
        raw = io.BytesIO()
        with tarfile.open(fileobj=raw, mode="w", format=tarfile.PAX_FORMAT) as tar:
            payload = os.urandom(20000)
            info = tarfile.TarInfo("folder/file.bin")
            info.size = len(payload)
            info.mtime = 1_600_000_000
            tar.addfile(info, io.BytesIO(payload))
        data = raw.getvalue()
        cuts = [0, 1000, 7000, len(data)]
        for i in range(3):
            (folder / "old.tar.{:03d}".format(i + 1)).write_bytes(data[cuts[i]:cuts[i + 1]])
        (folder / "old.tar.sha256").write_text("{}  old.tar\n".format(hashlib.sha256(data).hexdigest()))
        return folder, data, payload

    def test_extract_and_merge_only(self):
        folder, data, payload = self.make_legacy()
        extracted = self.tmp / "legacy-restored"
        tg.join_files(folder, extracted, log=lambda s: None)
        self.assertEqual((extracted / "folder" / "file.bin").read_bytes(), payload)
        merged = self.tmp / "legacy-merged"
        result = tg.join_dispatch([folder], merged, merge_only=True, log=lambda s: None)
        self.assertEqual(result[0].read_bytes(), data)
        cli_out = self.tmp / "legacy-cli"
        self.assertEqual(tg.main(["join", str(folder / "old.tar.002"), "-o", str(cli_out)]), 0)
        self.assertEqual((cli_out / "folder" / "file.bin").read_bytes(), payload)


class ExtendTests(TempCase):
    def test_new_files_and_done_move_without_rebuilding_old_archives(self):
        root = self.tree("ext")
        a_data = os.urandom(180 * 1024)
        c_data = os.urandom(100 * 1024 + 3)
        (root / "a").write_bytes(a_data)
        (root / "b").write_bytes(os.urandom(400 * 1024))
        out = self.tmp / "ext-out"
        original = tg.split_plan([root], out, 300 * 1024, "ext", log=lambda s: None)
        old_count = len(original["archives"])
        old_hashes = {a["index"]: tg.hash_file(tg.archive_path(out, original, a["index"]))
                      for a in original["archives"]}
        moved_dir = root / "moved"
        moved_dir.mkdir()
        (root / "a").rename(moved_dir / "renamed-a")
        (root / "c").write_bytes(c_data)
        (root / "new-empty").mkdir()
        extended = tg.extend_plan(out, "ext", plan_only=True, log=lambda s: None)
        self.assertEqual(extended["plan_id"], original["plan_id"])
        self.assertGreater(len(extended["archives"]), old_count)
        self.assertEqual(extended["extensions"][0]["moves"],
                         [{"type": "move", "source": "ext/a", "target": "ext/moved/renamed-a"}])
        for index, digest in old_hashes.items():
            self.assertEqual(tg.hash_file(tg.archive_path(out, extended, index)), digest)
        self.assertTrue(all(a["status"] == "pending" for a in extended["archives"][old_count:]))
        tg.split_plan([], out, name="ext", log=lambda s: None)
        archives = [tg.archive_path(out, extended, i) for i in range(1, len(extended["archives"]) + 1)]
        restored = self.tmp / "ext-restored"
        tg.restore_archives([archives[-1]], restored, log=lambda s: None)
        self.assertFalse((restored / "ext" / "moved" / "renamed-a").exists())
        report = tg.restore_archives(list(reversed(archives[:-1])), restored, log=lambda s: None)
        self.assertEqual(report["incomplete"], [])
        self.assertFalse((restored / "ext" / "a").exists())
        self.assertEqual((restored / "ext" / "moved" / "renamed-a").read_bytes(), a_data)
        self.assertEqual((restored / "ext" / "c").read_bytes(), c_data)
        self.assertTrue((restored / "ext" / "new-empty").is_dir())
        self.assertIn("ext/moved/renamed-a", report["complete"])

    def test_move_of_pending_source_and_second_extension(self):
        root = self.tree("pending-ext")
        b_data = os.urandom(410 * 1024 + 7)
        (root / "a").write_bytes(os.urandom(180 * 1024))
        (root / "b").write_bytes(b_data)
        out = self.tmp / "pending-ext-out"
        tg.split_plan([root], out, 300 * 1024, "pending-ext", max_parts=1, log=lambda s: None)
        (root / "b").rename(root / "b-moved")
        first = tg.extend_plan(out, "pending-ext", plan_only=True, log=lambda s: None)
        moved_record = next(f for f in first["files"] if f["path"] == "pending-ext/b")
        self.assertEqual(moved_record["source"], str(root / "b-moved"))
        tg.split_plan([], out, name="pending-ext", log=lambda s: None)
        restored = self.tmp / "pending-ext-restored"
        tg.restore_archives([out], restored, log=lambda s: None)
        self.assertEqual((restored / "pending-ext" / "b-moved").read_bytes(), b_data)
        self.assertFalse((restored / "pending-ext" / "b").exists())
        before = len(first["archives"])
        same = tg.extend_plan(out, "pending-ext", plan_only=True, log=lambda s: None)
        self.assertEqual(len(same["archives"]), before)
        (root / "second").write_bytes(b"second extension")
        second = tg.extend_plan(out, "pending-ext", plan_only=True, log=lambda s: None)
        self.assertGreater(len(second["archives"]), before)
        self.assertEqual(second["plan_id"], first["plan_id"])

    def test_move_chain_applies_when_operation_archives_arrive_first(self):
        root = self.tree("chain")
        (root / "a").write_bytes(b"chain data")
        out = self.tmp / "chain-out"
        original = tg.split_plan([root], out, 300 * 1024, "chain", log=lambda s: None)
        original_archive = tg.archive_path(out, original, 1)
        (root / "a").rename(root / "b")
        first = tg.extend_plan(out, "chain", log=lambda s: None)
        first_move = tg.archive_path(out, first, first["extensions"][-1]["archives"][-1])
        (root / "b").rename(root / "c")
        second = tg.extend_plan(out, "chain", log=lambda s: None)
        second_move = tg.archive_path(out, second, second["extensions"][-1]["archives"][-1])
        restored = self.tmp / "chain-restored"
        tg.restore_archives([second_move], restored, log=lambda s: None)
        tg.restore_archives([first_move], restored, log=lambda s: None)
        tg.restore_archives([original_archive], restored, log=lambda s: None)
        self.assertEqual((restored / "chain" / "c").read_bytes(), b"chain data")
        self.assertFalse((restored / "chain" / "a").exists())
        self.assertFalse((restored / "chain" / "b").exists())

    def test_extend_cli_max_parts_only_uses_new_archives(self):
        root = self.tree("ext-cli")
        (root / "old").write_bytes(b"old")
        out = self.tmp / "ext-cli-out"
        tg.split_plan([root], out, 300 * 1024, "ext-cli", log=lambda s: None)
        (root / "new-a").write_bytes(os.urandom(350 * 1024))
        (root / "new-b").write_bytes(os.urandom(350 * 1024))
        self.assertEqual(tg.main(["extend", "-o", str(out), "--max-parts", "1"]), 0)
        plan = tg.load_plan(out)
        extension = plan["extensions"][-1]
        self.assertEqual(plan["archives"][extension["archives"][0] - 1]["status"], "done")
        self.assertTrue(any(plan["archives"][i - 1]["status"] == "pending"
                            for i in extension["archives"][1:]))
        self.assertEqual(tg.build_parser().parse_args(["extend", "-o", "x", "--plan-only"]).plan_only, True)


class GuiTests(TempCase):
    def test_resume_summary_and_parser(self):
        root = self.tree("gui")
        (root / "f").write_bytes(b"data")
        out = self.tmp / "gui-out"
        plan = tg.make_plan([root], out, 300 * 1024, "gui", log=lambda s: None)
        self.assertIn("Готово 0 из 1", tg.gui_plan_summary(plan))
        plan = tg.split_plan([root], out, 300 * 1024, "gui", log=lambda s: None)
        self.assertIn("Готово 1 из 1", tg.gui_plan_summary(plan))
        self.assertEqual(tg.build_parser().parse_args(["gui"]).cmd, "gui")
        self.assertEqual(tg.build_parser().parse_args(["split", "-o", "out", "--max-parts", "5"]).max_parts, 5)

    def test_tkinter_initialization(self):
        try:
            import tkinter as tk
        except ImportError as e:
            self.skipTest("Tk unavailable: {}".format(e))
        try:
            root = tk.Tk()
            root.withdraw()
            root.update_idletasks()
            root.destroy()
        except tk.TclError as e:
            self.skipTest("Display unavailable: {}".format(e))


class FinalBehaviorTests(TempCase):
    def test_recreate_lost_plan_and_recover_present_archive(self):
        root = self.tree("recover")
        (root / "a").write_bytes(os.urandom(180 * 1024))
        (root / "b").write_bytes(os.urandom(400 * 1024))
        out = self.tmp / "recover-out"
        original = tg.split_plan([root], out, 300 * 1024, "recover", max_parts=1, log=lambda s: None)
        expected_hash = original["archives"][0]["sha256"]
        (out / "recover.plan.json").unlink()
        recovered = tg.create_plan([root], out, 300 * 1024, "recover", log=lambda s: None, recover=True)
        self.assertEqual(recovered["plan_id"], original["plan_id"])
        self.assertEqual(recovered["archives"][0]["status"], "done")
        self.assertEqual(recovered["archives"][0]["sha256"], expected_hash)
        self.assertEqual(recovered["archives"][1]["status"], "pending")

    def test_new_source_warned_and_ignored(self):
        root = self.tree("new-source")
        (root / "a").write_bytes(os.urandom(180 * 1024))
        (root / "b").write_bytes(os.urandom(400 * 1024))
        out = self.tmp / "new-source-out"
        tg.split_plan([root], out, 300 * 1024, "new", max_parts=1, log=lambda s: None)
        (root / "new-file").write_bytes(b"ignore me")
        messages = []
        plan = tg.split_plan([], out, name="new", log=messages.append)
        self.assertTrue(any("проигнорирован" in m for m in messages))
        self.assertNotIn("new/new-file", {f["path"] for f in plan["files"]})

    def test_on_exist_skip_and_rename(self):
        root = self.tree("existing")
        (root / "f").write_bytes(b"new data")
        out = self.tmp / "existing-out"
        tg.split_plan([root], out, 300 * 1024, "existing", log=lambda s: None)
        archive = out / "existing.0001.tar"
        dest = self.tmp / "existing-restored"
        target = dest / "existing" / "f"
        target.parent.mkdir(parents=True)
        target.write_bytes(b"old")
        tg.restore_archives([archive], dest, on_exist="skip", log=lambda s: None)
        self.assertEqual(target.read_bytes(), b"old")
        tg.restore_archives([archive], dest, on_exist="rename", log=lambda s: None)
        self.assertEqual(Path(str(target) + "_2").read_bytes(), b"new data")


@unittest.skipUnless(os.environ.get("TGSPLIT_LARGE_SMOKE"), "set TGSPLIT_LARGE_SMOKE=1 for multi-GB smoke")
class LargeSparseSmokeTest(TempCase):
    def test_real_1900m_split_restore_memory_and_speed(self):
        import tracemalloc
        source = self.tmp / "large"
        source.mkdir()
        data = source / "sparse.bin"
        size = 2 * tg.DEFAULT_PART_SIZE + 12345
        with open(str(data), "wb") as f:
            f.seek(size - 1)
            f.write(b"\0")
        out = self.tmp / "large-out"
        tracemalloc.start()
        started = time.monotonic()
        plan = tg.split_plan([source], out, tg.DEFAULT_PART_SIZE, "large", log=lambda s: None)
        split_seconds = time.monotonic() - started
        self.assertEqual(len(plan["archives"]), 4)
        self.assertTrue(all(a["size"] <= tg.DEFAULT_PART_SIZE for a in plan["archives"]))
        restored = self.tmp / "large-restored"
        restore_started = time.monotonic()
        report = tg.restore_archives([out], restored, log=lambda s: None)
        restore_seconds = time.monotonic() - restore_started
        _, python_peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        self.assertEqual(report["incomplete"], [])
        result = restored / "large" / "sparse.bin"
        self.assertEqual(result.stat().st_size, size)
        self.assertEqual(tg.hash_file(result), tg.hash_file(data))
        process_peak = None
        if os.name == "nt":
            import ctypes
            from ctypes import wintypes

            class Counters(ctypes.Structure):
                _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD),
                            ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                            ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                            ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                            ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t)]

            counters = Counters()
            counters.cb = ctypes.sizeof(counters)
            if ctypes.windll.psapi.GetProcessMemoryInfo(ctypes.windll.kernel32.GetCurrentProcess(),
                                                        ctypes.byref(counters), counters.cb):
                process_peak = counters.PeakWorkingSetSize
        self.assertLess(python_peak, 64 * tg.MiB)
        print("LARGE_SMOKE bytes={} split={:.2f}s ({:.1f} MiB/s) restore={:.2f}s ({:.1f} MiB/s) "
              "python_peak={} process_peak={}".format(
                  size, split_seconds, size / tg.MiB / split_seconds,
                  restore_seconds, size / tg.MiB / restore_seconds,
                  tg.human(python_peak), tg.human(process_peak) if process_peak else "unknown"))


if __name__ == "__main__":
    unittest.main(verbosity=2)