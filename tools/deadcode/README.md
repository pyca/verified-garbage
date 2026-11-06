# Finding and removing dead Lean code

These scripts are not part of the library; they live on this branch only so
that parallel sessions can share them. Copy them into your scratchpad (`WORK`)
and run them from the repository root (`REPO`, default: the current
directory). They were used for #4305 (DSA) and #4314 (ECDSA); read those PRs'
descriptions for the shape of a result.

## Method

A declaration is dead when nothing reachable from the roots refers to it,
directly or transitively. Roots: every declaration in `Artifacts/`,
`Generic/`, `Variants/`, `TCB/` and `VerifiedGarbageTest/`, the non-Spec
modules the lakefile names, and the modules the top-level `*.lean` files
import.

`.ilean` files record syntactic references only, so three kinds of use are
invisible and the rules below keep them:

1. **Literals found by name.** `rw_lit`, `lit_decide` and `taint_decide` find
   `materialize_*` literals by name. Every module-level command of a module
   the roots import is live, with what it references (`live4.py`). Lit
   modules that live code imports stay, with the code they materialize.
2. **Tactics, macros and notation.** A module that defines syntax is never
   deleted (`plan2.py`); its dead declarations may be trimmed. (ECDSA's
   `JacChecks` looked dead but defines tactics live proofs use.)
3. **Attributes and instances.** A declaration with an attribute (simp sets,
   instances, ...) in a module the roots import is live. `irreducible`,
   `inline` and the like do not count.

The full `lake build` is the arbiter: the analysis proposes, the build
decides.

## Steps

```sh
export REPO=$PWD WORK=<scratchpad dir> SCOPE=Weierstrass   # comma-separated
# 1. A fresh, complete build at HEAD (restore the CI cache first, CLAUDE.md).
(cd lean && lake build --log-level=warning)
# 2. Graph and live set.
python3 tools/deadcode/graph2.py $WORK/g_head.pkl          # ~2.5 min
python3 tools/deadcode/live4.py $WORK/g_head.pkl $WORK/l.pkl
python3 tools/deadcode/measure.py $WORK/g_head.pkl $WORK/l.pkl   # per-algorithm counts
# 3. Plan, then iterate live4 with the plan's deletions left out until stable.
python3 tools/deadcode/plan2.py g_head.pkl l.pkl                 # paths relative to WORK
python3 tools/deadcode/live4.py $WORK/g_head.pkl $WORK/l2.pkl $WORK/plan.pkl
python3 tools/deadcode/plan2.py g_head.pkl l2.pkl plan.pkl       # repeat to a fixed point
# 4. Apply to an unmodified tree (it refuses a dirty one), then fix up.
python3 tools/deadcode/apply.py
python3 tools/deadcode/docrefs.py ...    # doc comments naming removed names
```

`SRC` may point at a separate checkout of the graph's revision so the
analysis does not read a tree you are editing.

## Rules

* Remove only declarations and modules under `Proof/<Alg>/` and
  `Impl/<Alg>/` for the algorithms in your scope. Never touch `Spec/` or
  `TCB/` (trust changes, their own PR).
* Keep any declaration that something outside the removal set refers to
  (another algorithm's code, even dead code there: a later pass removes it).
* Never delete a module another algorithm's registration (`Artifacts/`,
  `Generic/`, `Variants/`) imports; trim it instead.
* In registration files, only drop imports of deleted modules
  (`check_registrations.py`).
* When a deleted module passed imports on, its importers import what they
  use directly (see the `lean-modules` skill). Remove dangling
  `open … in`, `omit … in`, empty sections and namespaces.
* Reword doc comments that name removed declarations.
* `Emit.lean --check` must pass unchanged: no generated crate changes.
* Never run two `lake build`s at once (they corrupt `.olean`s). `lake` is in
  `~/.elan/bin`; put it on `PATH` for scripts (`check_lean_public_imports.py`
  runs it).
* Top-level `Verified` proofs of routines no registration exports are dead
  like any other declaration: list them in the PR description.

## Checks before opening the PR

* full `lake build --log-level=warning`, then
  `sysctl -w vm.max_map_count=262144` and `lake env lean --run Emit.lean --check`;
* every Static checks step of `.github/workflows/ci.yml`, with
  `check_lean_single_importer.py --base origin/main`;
* `check_lean_public_imports.py --base origin/main -m <modified modules>`;
* `cargo fmt --check` and `cargo clippy --all-targets -- -D warnings`;
* rerun the analysis: nothing dead left in scope beyond what you kept for a
  stated reason.
