# omega_arith → minimal omega_using

Development tooling only: nothing here is imported by the library.

`omin.py` rewrites each `omega_arith` in a proof module to `omega_using [h₁, …]`
naming the fewest hypotheses `omega` needs at that call. It works on a scratch
copy and never edits the module itself.

1. It pastes `omin_header.lean` (an `omega_min` elaborator) into a copy of the
   module, after its imports.
2. It replaces every `omega_arith` in the copy with `omega_min`.
3. It compiles the copy once. At each call, `omega_min` starts from the facts
   `omega_arith` would use (falling back to every arithmetic fact), drops facts
   one at a time while `omega` still succeeds, and logs the survivors with
   their position.
4. If a survivor has no usable name (hygienic, or shadowed by a later
   hypothesis of the same name), that call keeps `omega_arith`.
5. It writes the module's text with each `omega_arith` replaced by its
   logged `omega_using [...]`.

The header sets `maxHeartbeats 0`, but only in the scratch copy; the minimized
file has no such option.

```sh
cd lean
python3 ../tools-omin/omin.py VerifiedGarbage/Proof/Foo/Bar.lean /tmp/Bar.lean
#   replaced 91, kept 5; facts per call: [...]
```

Then compile `/tmp/Bar.lean` against the module's setup and check that Lean
reports zero errors. Compare heartbeats with the original before copying the
result over the module.

`omin.py` still uses this session's scratchpad paths: set `S` (the directory
holding `omin_header.lean`) and `lean_dir` at its top to yours. It reuses or
creates `.lake/setup_<module>.json`, so the module's imports must be built
(restore the CI cache first).

Example: on `Proof/Modes/X86_64/CbcGroup.lean` it rewrote 91 of 96 calls, each
keeping 0–5 facts. Heartbeats went from 68.0M to 53.5M and kernel from 12.4M
to 7.5M.
