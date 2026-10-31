"""Where the generated code of each target is.

The emitter writes each target's verified functions as a crate of its own,
`crates/verified-garbage-asm-<target>/`: its root `src/lib.rs` and a file
`src/<module>.rs` per module (and `src/consts/`, the tables of constants).
Before, they were modules of the library, `src/asm/<target>/` (with root
`mod.rs`), as they still are at older revisions, which the scripts that
compare a change with its base read too.

So that those scripts need not know both, each speaks of a generated file
by its path in the library's layout, `src/asm/<target>/<file>` (`logical`),
and reads it wherever the tree or revision has it (`physical`).
"""

import pathlib
import re

CRATES = "crates"
PREFIX = "verified-garbage-asm-"

# A file of a target's crate: its target and its path in the crate's `src/`.
CRATE_FILE = re.compile(rf"^{CRATES}/{PREFIX}([a-z0-9_]+)/src/(.+)$")


def logical(path):
    """`path` (repository-relative, `/`-separated) as a path of the library's
    layout: a file of a target's crate as `src/asm/<target>/<file>`, its root
    `lib.rs` as `mod.rs`; any other path as it is."""
    m = CRATE_FILE.match(path)
    if not m:
        return path
    target, rest = m.groups()
    return f"src/asm/{target}/{'mod.rs' if rest == 'lib.rs' else rest}"


def physical(path):
    """Where a file of the library's layout (`logical`) may be: in its
    target's crate, then where it was; any other path as it is."""
    m = re.match(r"^src/asm/([a-z0-9_]+)/(.+)$", path)
    if not m:
        return [path]
    target, rest = m.groups()
    crate = f"{CRATES}/{PREFIX}{target}/src/{'lib.rs' if rest == 'mod.rs' else rest}"
    return [crate, path]


def target_dir(root, target):
    """The directory of `target`'s generated modules under `root`: its
    crate's `src/`, or, before that, `src/asm/<target>/`."""
    crate = pathlib.Path(root) / CRATES / f"{PREFIX}{target}" / "src"
    return crate if crate.is_dir() else pathlib.Path(root) / "src" / "asm" / target


def target_dirs(root):
    """Each target's directory of generated modules under `root`, by its
    name, in either layout."""
    dirs = {}
    old = pathlib.Path(root) / "src" / "asm"
    if old.is_dir():
        dirs.update({p.name: p for p in old.iterdir() if p.is_dir()})
    crates = pathlib.Path(root) / CRATES
    if crates.is_dir():
        dirs.update({p.name[len(PREFIX):]: p / "src" for p in crates.iterdir()
                     if p.name.startswith(PREFIX) and (p / "src").is_dir()})
    return dict(sorted(dirs.items()))


def generated_files(root):
    """Every generated `.rs` file under `root`, in either layout, by its
    logical path, with its real path."""
    files = {}
    old = pathlib.Path(root) / "src" / "asm"
    crates = pathlib.Path(root) / CRATES
    paths = list(old.glob("**/*.rs")) if old.is_dir() else []
    if crates.is_dir():
        paths += [p for p in crates.glob(f"{PREFIX}*/src/**/*.rs")]
    for p in paths:
        files[logical(p.relative_to(root).as_posix())] = p
    return dict(sorted(files.items()))
