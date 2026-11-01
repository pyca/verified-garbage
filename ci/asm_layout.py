"""Where the generated code of each target is.

The emitter writes each target's verified functions into a crate of its
own, `crates/verified-garbage-asm-<target>/src/`: its root `lib.rs` and a
file `<module>.rs` per module (and `consts/`, the tables of constants).

`bench_arches.py` names a generated file by the path the library gave it
before the crates, `src/asm/<target>/<file>` (with root `mod.rs`):
`logical` gives that name of a crate's file, and `physical` the crate's
file of that name.
"""

import pathlib
import re

CRATES = "crates"
PREFIX = "verified-garbage-asm-"

# A file of a target's crate's `src/`: its target and its path there.
CRATE_FILE = re.compile(rf"^{CRATES}/{PREFIX}([a-z0-9_]+)/src/(.+)$")


def logical(path):
    """`path` (repository-relative, `/`-separated) by its name in the
    library's layout: a file of a target's crate as `src/asm/<target>/<file>`,
    its root `lib.rs` as `mod.rs`; any other path as it is."""
    m = CRATE_FILE.match(path)
    if not m:
        return path
    target, rest = m.groups()
    return f"src/asm/{target}/{'mod.rs' if rest == 'lib.rs' else rest}"


def physical(path):
    """The file of a target's crate that `path` names in the library's layout
    (`logical`); any other path as it is."""
    m = re.match(r"^src/asm/([a-z0-9_]+)/(.+)$", path)
    if not m:
        return path
    target, rest = m.groups()
    return f"{CRATES}/{PREFIX}{target}/src/{'lib.rs' if rest == 'mod.rs' else rest}"


def target_dir(root, target):
    """The directory of `target`'s generated modules under `root`."""
    return pathlib.Path(root) / CRATES / f"{PREFIX}{target}" / "src"


def target_dirs(root):
    """Each target's directory of generated modules under `root`, by its
    name: those of the crates that have one."""
    crates = pathlib.Path(root) / CRATES
    if not crates.is_dir():
        return {}
    return {p.name[len(PREFIX):]: p / "src" for p in sorted(crates.iterdir())
            if p.name.startswith(PREFIX) and (p / "src" / "lib.rs").is_file()}


def generated_files(root):
    """Every generated `.rs` file under `root`, by its name in the library's
    layout (`logical`), with its real path."""
    paths = [p for d in target_dirs(root).values() for p in d.glob("**/*.rs")]
    return dict(sorted((logical(p.relative_to(root).as_posix()), p) for p in paths))
