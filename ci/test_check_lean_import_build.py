"""Real subprocess tests for bounded build cancellation and attempt records."""

import fcntl
import pathlib
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
import unittest

import lean_import_build as build


# A child that holds an exclusive lock on `lock` for as long as it lives, then
# says it is ready: the kernel releases the lock when the child exits.
CHILD = ("import fcntl,pathlib,time; f=open({lock!r},'w'); fcntl.flock(f, fcntl.LOCK_EX); "
         "pathlib.Path({ready!r}).write_text('ready'); time.sleep(30)")


class Builds(unittest.TestCase):
    def assertExited(self, lock, message):
        """Asserts that the child holding `lock` exits within a few seconds:
        the test waits only as long as the kill takes, not a fixed sleep."""
        with open(lock) as f:
            deadline = time.monotonic() + 5
            while True:
                try:
                    fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    return
                except BlockingIOError:
                    if time.monotonic() > deadline:
                        self.fail(message)
                    time.sleep(0.01)

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.log = self.root / "build.log"

    def test_success_records_actual_rebuilds(self):
        attempt = build.Attempt("verify", ["A"], str(self.log))
        result = build.command([sys.executable, "-c", "print('✔ [1/1] Built A (123ms)')"],
                               self.root, self.log, attempt, 5)
        self.assertTrue(result.succeeded)
        self.assertEqual(result.rebuilt, ["A"])
        self.assertFalse(result.failures)
        self.assertGreater(result.elapsed_seconds, 0)

    def test_failed_build_records_modules_and_exit_status(self):
        attempt = build.Attempt("verify", ["A"], str(self.log))
        result = build.command([sys.executable, "-c", "print('✖ [1/1] Building A'); raise SystemExit(1)"],
                               self.root, self.log, attempt, 5)
        self.assertFalse(result.succeeded)
        self.assertEqual(result.failures, ["A"])
        self.assertEqual(result.returncode, 1)

    def test_timeout_kills_a_child_which_ignores_sigterm(self):
        ready, lock = self.root / "ready", self.root / "lock"
        child = ("import signal; signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                 + CHILD.format(lock=str(lock), ready=str(ready)))
        parent = f"import subprocess,sys,time; subprocess.Popen([sys.executable,'-c',{child!r}]); time.sleep(30)"
        attempt = build.Attempt("verify", ["A"], str(self.log))
        result = build.command([sys.executable, "-c", parent], self.root, self.log, attempt, 0.3)
        self.assertTrue(result.timed_out)
        self.assertFalse(result.succeeded)
        self.assertTrue(ready.is_file(), "the test child must have started")
        self.assertExited(lock, "a surviving child could write stale build outputs after rollback")

    def test_sigterm_unwinds_and_stops_the_separate_build_group(self):
        ready, lock = self.root / "ready", self.root / "lock"
        result = self.root / "result.json"
        child = CHILD.format(lock=str(lock), ready=str(ready))
        script = ("import sys,pathlib; "
                  f"sys.path.insert(0, {str(pathlib.Path(build.__file__).parent)!r}); "
                  "import lean_import_build as b\n"
                  f"a=b.Attempt('verify', ['A'], {str(self.log)!r})\n"
                  "try:\n"
                  f" b.command([sys.executable,'-c',{child!r}],pathlib.Path({str(self.root)!r}),pathlib.Path(a.log),a)\n"
                  "finally:\n"
                  f" b.save(pathlib.Path({str(result)!r}),a.json())\n")
        parent = subprocess.Popen([sys.executable, "-c", script], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.addCleanup(lambda: parent.poll() is None and parent.kill())
        deadline = time.monotonic() + 5
        while not ready.exists() and parent.poll() is None and time.monotonic() < deadline:
            time.sleep(0.01)
        self.assertTrue(ready.exists(), "build child did not start")
        os.kill(parent.pid, signal.SIGTERM)
        parent.wait(timeout=8)
        data = json.loads(result.read_text())
        self.assertTrue(data["interrupted"])
        self.assertFalse(data["succeeded"])
        self.assertExited(lock, "SIGTERM left the separate Lean process group running")


if __name__ == "__main__":
    unittest.main()
