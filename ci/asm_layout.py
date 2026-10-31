"""Where the generated code of each target is.

The emitter writes each target's verified functions, as printed, into a
crate of its own, `crates/verified-garbage-asm-<target>/asm/`: its root
`lib.rs` and a file `<module>.rs` per module (and `consts/`, the tables of
constants). Before, the crate had them in `src/`, and before that they were
modules of the library, `src/asm/<target>/` (with root `mod.rs`), as they
still are at older revisions, which the scripts that compare a change with
its base read too.

So that those scripts need not know every layout, each speaks of a
generated file by its path in the library's layout,
`src/asm/<target>/<file>` (`logical`), and reads it wherever the tree or
revision has it (`physical`): the printed code, which a crate keeps in
`asm/` when it has one.
"""

import pathlib
import re

CRATES = "crates"
PREFIX = "verified-garbage-asm-"
# A crate's directories of generated code: the printed code, then where it
# was before.
CODE_DIRS = ("asm", "src")

# A file of a target's crate: its target and its path in the crate's `asm/`
# (or `src/`).
CRATE_FILE = re.compile(rf"^{CRATES}/{PREFIX}([a-z0-9_]+)/(?:asm|src)/(.+)$")


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
    target's crate's `asm/`, then its `src/`, then where it was; any other
    path as it is."""
    m = re.match(r"^src/asm/([a-z0-9_]+)/(.+)$", path)
    if not m:
        return [path]
    target, rest = m.groups()
    name = "lib.rs" if rest == "mod.rs" else rest
    return [f"{CRATES}/{PREFIX}{target}/{d}/{name}" for d in CODE_DIRS] + [path]


def crate_code(crate):
    """The directory of a crate's printed code: its `asm/`, or, before that,
    its `src/`; `None` if it has neither."""
    for d in CODE_DIRS:
        if (crate / d).is_dir():
            return crate / d
    return None


def target_dir(root, target):
    """The directory of `target`'s generated modules under `root`: its
    crate's (`crate_code`), or, before that, `src/asm/<target>/`."""
    code = crate_code(pathlib.Path(root) / CRATES / f"{PREFIX}{target}")
    return code or pathlib.Path(root) / "src" / "asm" / target


def target_dirs(root):
    """Each target's directory of generated modules under `root`, by its
    name, in any layout."""
    dirs = {}
    old = pathlib.Path(root) / "src" / "asm"
    if old.is_dir():
        dirs.update({p.name: p for p in old.iterdir() if p.is_dir()})
    crates = pathlib.Path(root) / CRATES
    if crates.is_dir():
        for p in crates.iterdir():
            if p.name.startswith(PREFIX) and (code := crate_code(p)):
                dirs[p.name[len(PREFIX):]] = code
    return dict(sorted(dirs.items()))


def generated_files(root):
    """Every generated `.rs` file under `root`, in any layout, by its logical
    path, with its real path."""
    old = pathlib.Path(root) / "src" / "asm"
    paths = list(old.glob("**/*.rs")) if old.is_dir() else []
    for d in target_dirs(root).values():
        if d.parent.name.startswith(PREFIX):
            paths += d.glob("**/*.rs")
    return dict(sorted((logical(p.relative_to(root).as_posix()), p) for p in paths))
