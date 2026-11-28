"""Building and running the benchmark binary (bench/benches/primitives),
for the scripts that measure with it: ci/bench_compare.py and
ci/bench_publish.py.
"""

import json
import pathlib
import re
import shutil
import subprocess


def build(crate, env, features=""):
    """Builds the benchmark crate at `crate` (with its `features`,
    comma-separated), returning the binary's path."""
    out = subprocess.run(
        ["cargo", "bench", "--no-run", "--message-format=json-render-diagnostics",
         *(["--features", features] if features else [])],
        cwd=crate,
        env=env,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    for line in out.splitlines():
        msg = json.loads(line)
        if msg.get("reason") == "compiler-artifact" and msg.get("executable"):
            if msg["target"]["name"] == "primitives":
                return pathlib.Path(msg["executable"])
    raise RuntimeError(f"no benchmark binary built in {crate}")


def fresh_copy(binary, copy):
    """A copy of `binary` in the new file `copy`: the page cache holds a
    file's pages by inode, so the copy's code and tables are read into newly
    chosen physical pages."""
    copy = pathlib.Path(copy)
    shutil.copyfile(binary, copy)
    copy.chmod(0o755)
    return copy


def criterion(binary, home, warm_up_time, measurement_time, args, env, prefix=()):
    """Runs the benchmarks of `binary` that Criterion's `args` select (a
    filter, its other options), with its results under `home`, behind the
    command `prefix` (`taskset`, ...); returns the finished process, with its
    output and errors as text."""
    return subprocess.run(
        [*prefix, str(binary), "--bench", "--warm-up-time", str(warm_up_time),
         "--measurement-time", str(measurement_time), *args],
        env={**env, "CRITERION_HOME": str(home)},
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


def cpu_model():
    """This machine's CPU model, from /proc/cpuinfo (or, on macOS, `sysctl`),
    or None."""
    try:
        cpuinfo = pathlib.Path("/proc/cpuinfo").read_text()
    except OSError:
        try:
            out = subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True,
                                 text=True, check=True).stdout.strip()
        except (OSError, subprocess.CalledProcessError):
            return None
        return out or None
    m = re.search(r"^model name\s*:\s*(.+)$", cpuinfo, re.M)
    if m:
        return m[1].strip()
    # Arm's /proc/cpuinfo names only the parts' numbers; lscpu names them.
    try:
        out = subprocess.run(["lscpu"], capture_output=True, text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError):
        return None
    return lscpu_model(out)


def lscpu_model(out):
    """The CPU model `lscpu` printed in `out` (the first, on a machine of
    several kinds of core), or None."""
    m = re.search(r"^Model name\s*:\s*(.+)$", out, re.M)
    return m[1].strip() if m and m[1].strip() != "-" else None
