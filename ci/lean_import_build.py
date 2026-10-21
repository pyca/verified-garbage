"""Bounded Lake builds with durable outcomes and process-group cancellation."""

from dataclasses import asdict, dataclass, field
from contextlib import contextmanager
from functools import wraps
import os
import json
import pathlib
import re
import signal
import subprocess
import time
import threading

FAILED = re.compile(r"^✖ \[\d+/\d+\] \w+ ([^\s:]+)", re.M)
REBUILT = re.compile(r"^✔ \[\d+/\d+\] Built (\S+) \(([^)]+)\)", re.M)


@contextmanager
def cancellation():
    """Turn SIGTERM into unwinding so nested build groups and edits clean up."""
    if threading.current_thread() is not threading.main_thread():
        yield
        return
    def interrupted(signum, frame):
        raise InterruptedError("terminated by SIGTERM")
    previous = signal.signal(signal.SIGTERM, interrupted)
    try:
        yield
    finally:
        signal.signal(signal.SIGTERM, previous)


def interruptible(function):
    @wraps(function)
    def run(*args, **kwargs):
        with cancellation():
            return function(*args, **kwargs)
    return run


@dataclass
class Attempt:
    phase: str
    targets: list[str]
    log: str
    returncode: int | None = None
    elapsed_seconds: float = 0
    timed_out: bool = False
    interrupted: bool = False
    error: str | None = None
    failures: list[str] = field(default_factory=list)
    rebuilt: list[str] = field(default_factory=list)

    @property
    def succeeded(self):
        return self.returncode == 0 and not self.timed_out and not self.interrupted and self.error is None

    def json(self):
        return {**asdict(self), "succeeded": self.succeeded}


def terminate(process):
    """Stop Lean children before restoring any source files."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    # The parent may have exited before a child that ignores SIGTERM. Kill
    # any remaining process-group members even after the parent was reaped.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


@interruptible
def command(args: list[str], cwd: pathlib.Path, log: pathlib.Path, attempt: Attempt,
            timeout: float | None = None) -> Attempt:
    """Run a build command; save the outcome even when interrupted."""
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    try:
        with log.open("w") as output:
            process = subprocess.Popen(args, cwd=cwd, stdout=output, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            try:
                attempt.returncode = process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                attempt.timed_out = True
                terminate(process)
                attempt.returncode = process.returncode
            except BaseException:
                attempt.interrupted = True
                terminate(process)
                attempt.returncode = process.returncode
                raise
    except BaseException as error:
        attempt.error = f"{type(error).__name__}: {error}"
        raise
    finally:
        attempt.elapsed_seconds = time.monotonic() - started
        if log.is_file():
            text = log.read_text(errors="replace")
            attempt.failures = sorted(set(FAILED.findall(text)))
            attempt.rebuilt = [name for name, _ in REBUILT.findall(text)]
    return attempt


def build(targets: list[str], cwd: pathlib.Path, log: pathlib.Path, phase: str,
          timeout: float | None = None, attempt: Attempt | None = None) -> Attempt:
    attempt = attempt or Attempt(phase=phase, targets=targets, log=str(log))
    return command(["lake", "--no-ansi", "build", "--log-level=warning", *("+" + m for m in targets)],
                   cwd, log, attempt, timeout)


def save(path: pathlib.Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")
    tmp.replace(path)
