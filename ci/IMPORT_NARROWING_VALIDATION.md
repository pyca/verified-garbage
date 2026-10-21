# Import planner validation — 2026-10-21

Tested with Lean 4.35.0 against repository base
`5a6f9f346cd5d2dac526a89c50af3dfc1752b26e`. Live experiments used an isolated
worktree: build the original targets, apply the plan, build the affected library
closure in small chunks, then restore and rebuild the originals. This PR changes
tooling, tests and documentation; it includes no library or assembly edits.

## Results

| Check | Result |
| --- | --- |
| Final Python/Lean regression suite | 417 passed, zero skips; includes 42 compiled Lean tests |
| Final isolated proof sweep | 226 trials, 779 distinct selected modules; 67 verified trials, 259 operations kept, zero rollback |
| Larger sources within that sweep | 32 sources, approximately 35–145 KB; 132 operations kept, zero rollback |
| Final cumulative interaction trial | 34 roots, 643 operations kept, zero rollback; originals restored across 671 targets |
| Fresh representative proof sample | 331 operations kept; all 14 verification targets restored and rebuilt |
| Distinct final-runtime live coverage | 189 modules with verified edits, 833 library verification targets, 716 successfully rebuilt tasks |
| Generated projects | 192 projects, 2,335 verified operations; evaluated values preserved in instance/initializer cases |
| Portable replay | All 192 generated plans identical with process launches and original-source access disabled |

The generated total includes 160 projects compiled with the preceding runtime
and replayed unchanged with the final runtime, plus 32 freshly compiled final
projects. Counts above overlap: operations are executable edits, not net removed
imports, and verification targets can be up to date. They are not a full rebuild.

Scoped emitter comparisons passed before and after the cumulative Md5.X86 and
Sha512.X86 plans and complete Argon2/BLAKE2b caller/callee bundles on AArch64 and
x86-64. Incomplete Argon2 selections failed on missing callees in the unchanged
baseline; these were excluded from passing comparisons. Repository import,
module-layout, registration and Lean-speed checks passed. An audit of 176 saved
accepted patches found only import-command changes and no reviewed-directory
edits. Proof and assembly sources remained unchanged in the main checkout.

## Regressions found through iteration

| Failure | Protection now exercised |
| --- | --- |
| Real DSA exposed bodies depended on proof auxiliaries missed by shake | Follow generated auxiliaries, upgrading statement-only visits to body visits |
| Real Camellia narrowing lost generated instance evidence | Preserve opaque exported registries and erased elaboration effects |
| Real ML-DSA duplicated private/public imports | Edit the intended occurrence and validate the whole transaction |
| Private removal broke an `import all` consumer | Couple downstream ordinary/meta repairs to private removals too |
| Both versions compiled but instance-selected output changed from 2 to 1 | Preserve relative opaque-provider order and private initialization anchors |
| Compiling meta-import removal changed initialized output from 1 to 0 | Read raw IR initializer metadata, including macro-generated initializers |
| Compiling direct repair crossed an ARM/x86 boundary | Reuse repository target/layer policy; defer the responsible narrowing |

The last four rows use minimized/generated projects. Other compiled regressions
cover temporary simp/grind/Aesop use, empty namespaces, nested import comments,
phase visibility, pinned imports and coupled repairs at reviewed boundaries.

## Planning performance

On the same 331-operation capture, toggling only graph-closure reuse:

| Two repeats | Without reuse | With reuse |
| --- | --- | --- |
| Wall time | 118.82 s, 124.74 s | 8.45 s, 8.93 s |
| CPU time | 115.68 s, 116.25 s | 8.44 s, 8.91 s |
| Peak Python RSS | about 1.22 GiB | about 0.38 GiB |

All four report hashes matched; mean planning CPU improved 13.37×. Lean and Lake
were absent from replay's `PATH`. This measures planning, not proof-build speed.

## Reproduction and limits

Put the repository's Lean toolchain on `PATH`, then run:

```sh
python3 -m unittest discover -s ci -p 'test_check_*.py'
python3 ci/trim_lean_imports.py --replay ci/fixtures/import_narrowing/instance_order.json --report /tmp/import-order.json
python3 ci/stress_lean_imports.py --kind macro-initializers --projects 8 --seed 7312954 --output /tmp/import-stress
```

The [workflow guide](IMPORT_NARROWING.md) explains fresh captures, bounded live
verification, rejection caching and larger stress runs. Replays remain
unverified, and reader changes require fresh captures. Opaque effects, public
meta imports and `import all` impose conservative boundaries. The planner does
not establish globally minimal imports or general semantic equivalence of
arbitrary elaboration code; emitter checks remain separate.
