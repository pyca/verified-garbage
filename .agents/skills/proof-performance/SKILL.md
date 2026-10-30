---
name: proof-performance
description: "Use before writing or editing a Lean proof (symbolic execution, constant-time checks, kernel-evaluated code, imports of Mathlib), or when a proof is slow or near maxHeartbeats: the patterns to avoid and why, with the lemmas and tactics to use instead."
---

# Keeping proofs fast

"Keeping proofs fast" in `AGENTS.md` sums up each rule here in a line:
change the two together.

Lean's kernel re-checks every proof term, and it is a slow evaluator: most
of the build time used to be the kernel, not tactics.

Every declaration must elaborate and pass the kernel within Lean's default
`maxHeartbeats` (200000; the largest proof needs about half of that). Never
`set_option maxHeartbeats`, `maxRecDepth` or another resource limit, in a
source file or the lakefile: a proof that hits the limit is too slow, so make
it faster.
`ci/check_lean_speed.py` enforces this, and the rules below that can be
checked without building.

Avoid these patterns (each has cost tens of seconds in one proof):

* **Constant time:** use `VG.Taint.constantTime … (by taint_decide)`, never
  `decide +kernel` on a taint check: `taint_decide` precomputes loop
  invariants so the kernel does not search for them.
* **Symbolic execution:** step blocks with the ISA's `runBlock_cons`,
  `runStep_some` and `runBlock_nil` (`Proof/Framework/<ISA>/Exec.lean`), never
  `simp [runBlock]`, which runs the rest of the block from an unknown state
  after every instruction.
* **One symbolic execution per code shape:** don't case-split (e.g.
  `interval_cases` on a register rotation) and run the same block once per
  case; generalize what differs (see `round_ok` and `round_nodup`). Memory
  offsets generalize too: pass their bounds and separation from a lemma
  proved once (`round_sep`, x86), stating each pair in both orders, since
  `simp` won't match `a ∨ b` against `b ∨ a`.
* **Short symbolic executions:** don't run a long block of loads and stores
  in one `simp`; the states grow with every access. Prove one step for any
  index (`ld_ok k`, `upd_ok k`) and compose the steps by induction with
  `WP.block_append_iff`.
* **Kernel-evaluated data:** anything the kernel evaluates (a taint domain,
  a `decide +kernel` check) should use `Nat` arithmetic, which the kernel
  runs natively, not lists it searches element by element: sets of
  registers are `RegSet`s (`Proof/Framework/RegSet.lean`), not `List Reg`.
* **Finite facts:** prove a fact about a few small numbers with one `decide`
  on the bounded statement (`∀ j < 16, ∀ k < 16, wreg j = wreg k → j = k`),
  not `interval_cases j <;> interval_cases k <;> simp`. For a nested `if`
  on the same index on both sides, split the index into ranges once with
  `omega` and resolve each `if` with
  `simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]`, not `split_ifs`.
* **Nested `if`s under a discharger:** give `simp` the lemmas that resolve
  an `if` (`ite_eq_left`, `ite_eq_right`, a family's `ifp`/`ifn`) as
  pre-rewrites, `↓ite_eq_left`. Otherwise `simp` simplifies both branches of
  an `if` before the `if` itself, so its discharger (`omega`) runs, and
  usually fails twice, on the conditions of branches the outer `if` then
  discards; a failing `omega` is its slowest case (6–46% of a module's
  heartbeats in #2374). Lemmas that only rewrote inside those branches then
  show up as unused simp arguments: remove them.
* **Instruction lists under `++`:** in a theorem statement, ascribe each
  instruction-list literal next to `++`: `.block (absorb 1 ++
  ([.alu .add .esi (.imm 16)] : List Instr))`, not `absorb 1 ++ [.alu …]`.
  `++` elaborates its operands without an expected type, so every `.op`
  fails once and is elaborated again (up to seconds per statement).
* **Imports:** never import `Mathlib.Tactic` or all of Mathlib, which costs
  seconds in every module that (transitively) imports it: import the
  module of each tactic or lemma you use (e.g. `Mathlib.Tactic.IntervalCases`),
  and prefer core lemmas. The framework (`Proof/Framework/`) provides no
  Mathlib tactics, only Batteries' light ones (`by_contra`, `absurd`,
  `exacts`, `swap`, `<;> [t₁; t₂]`). `IntervalCases`, `NormNum`, `Ring` and
  `Mathlib.Data.List.*` each add about half a second to every module that
  imports them, even indirectly: keep them out of modules that many others
  import (a framework file, an algorithm's `Spec` or `Stream` lemmas).
  `ci/check_lean_speed.py` fails when a module importing heavy algebra
  (`HEAVY_MATHLIB`: `Ring`, `ZMod`, `NormNum`, `Linarith`, polynomials, …)
  is imported by more than 40 others; core `grind` proves the ring
  identities `ring` is used for.
* **Imports across targets:** a module of one target (a path with a
  directory of `TCB/`, e.g. `Proof/Sha256/Arm/…`) never imports a module of
  another target, even for a lemma that mentions no ISA: a change to one
  target (e.g. its ISA model) would then rebuild the other's proofs too, and
  a CI shard (`ci/lean_shards.py`), which builds a proof with everything it
  imports, would check both. Put what more than one target uses in
  a target-independent module (`Proof/<Alg>/…`, `Proof/Framework/…`);
  `ci/check_lean_imports.py` checks it. For the same reason `TCB/` is
  compiled as a precompiled library per target (`NativeTCB<Target>` in
  `lean/lakefile.toml`) and one for the rest (`NativeTCB`): a native module
  depends on the whole shared library of each library it imports from, so
  a new target gets its own, and a new file directly in `TCB/` is listed
  in `NativeTCB` (the same script checks both).
* **Properties of every instruction:** prove `(instrs c).all p` with
  `rw [← Code.allInstrs_eq]; decide +kernel`, not `decide +kernel` directly.
* **Code the kernel evaluates:** code built by functions (unrolled
  compression functions, and the functions calling them) is rebuilt by the
  kernel in every check that evaluates it (constant time, `spSafe`, …), in
  every module. Give it a literal: `materialize_code foo`
  (`Proof/Framework/Lit.lean`), in a `Lit.lean` next to its proofs, defines
  `foo.lit` and checks `foo.lit_eq` once; then `taint_decide` and
  `lit_decide` (not `decide +kernel`) evaluate the literal, and the
  registration file's `spSafe := Code.all_of_allInstrs (by lit_decide)`.
  Functions that build code or tables (a register allocator, spec
  tables) get literals too: `materialize_table f n` (for `f : Nat → α`;
  `Nat`-valued tables are packed into one number, read by a shift),
  `materialize_value c` (any value with `ToExpr`). `materialize_code`,
  `lit_decide` and `taint_decide` unfold the definitions that lead to any
  constant with a literal and read it, so a generator runs once, in its own
  `lit_eq`, if every module that evaluates code using it imports the module
  with its literal (a literal module imports the literal modules of the
  code it contains). Materializing code checked only once does not pay.
* **Constant time of many callers of the same function:** prove the
  callee's taint once as a summary (`taint_summary`, `taint_decide_sum`,
  `Proof/Framework/TaintSum.lean`) rather than analysing its body in every
  caller's `taint_decide`; this needs a `Taint.Frame` instance for the ISA's
  taint domain (so far `AArch64.VectorTaint`, `Framework/AArch64/TaintMono.lean`).
  A summary pays when declarations or modules share it: within one
  `taint_decide`, the kernel already analyses identical code from the same
  taint once, so splitting one check into summaries makes it slower. Give a
  summary the smallest taint its callers need (public slots that are never
  read back as addresses cost the kernel at every store). Code that differs
  only in immediates (table selections) has the same taint: check one copy
  (`Proof/Framework/AArch64/TaintErase.lean`, `constantTime_eraseImm_of_eq`).
* **Tactics run compiled:** a module defining tactics, elaborators,
  simprocs or `MetaM` functions that imports only Lean core and precompiled
  modules goes in `NativeTactics` (lakefile); the interpreter runs it an
  order of magnitude slower in every module that uses it
  (`ci/check_lean_speed.py` checks it). Mathlib tactics run interpreted:
  keep `tauto` and similar out of hot proofs.
* **Register reads after writes:** in symbolic execution never unfold
  `State.setReg` (`write`, `setFlags`, `arithFlags`, `setV`): the registers
  become a function that `simp` re-simplifies under a binder at every
  instruction, quadratic in the block's length. Read through the writes
  with `Proof/Framework/<ISA>/RegUpd.lean`: `gpr_setReg` (an `if`, decided
  for literal registers) or `gpr_setReg_self` and `gpr_setReg_of_ne` (for
  variables), and `mem_setReg`, `gpr_setFlags`, … for the other fields.
  Keep writes folded throughout the block; expand the final state once only
  if the postcondition needs it. Preserve this behavior in shared symbolic
  execution tactics so every caller benefits.
* **Frame facts through writes:** prove `s'.mem = s.mem` (and the other
  fields a frame keeps) for a state `s'` built by writes with the `RegUpd`
  lemmas given their arguments, or `simp only [mem_setV, …]` (`upd_frame` on
  AArch64), never `rfl` or a `.trans` chain of the lemmas with `_`
  arguments: unification unfolds the writes into structure literals and
  first tries to unify the states (seconds for a few vector instructions).
  On AArch64, `Proof/Framework/AArch64/Seal.lean` makes `State.setV`
  irreducible for elaboration in the modules that import it, which rules
  this out; import it once a module's proofs no longer unfold `setV`.
* **Addresses at offsets:** don't prove that ranges at `p + BitVec.ofNat 64 d`
  are separate, disjoint or contained, or their distances, with `bv_omega`
  (a second or more each, and a large term for the kernel): use `VG.Offset`
  (`Proof/Framework/Offset.lean`: `sep`, `disjoint`, `sub`, `contains_base`,
  …), whose hypotheses are about the offsets alone, closed by `omega` or,
  for literals, `decide`. Its identities (`add_add`, `add_sub_cancel_left`,
  `ofNat_sub_ofNat`, `sub_sub_eq`, …) are in `AddrArith.lean`, which `Mem`
  imports. A local lemma for a family's own ranges is one application of
  one of these, never a proof of its own.
* **`omega` in a large context:** `omega` and `bv_omega` look at every
  hypothesis, a tenth of a second or more each call in a long proof about
  states. Clear what they cannot use: `omega_arith`, `bv_omega_arith`
  (arithmetic hypotheses only) or `omega_using [h₁, …]`,
  `bv_omega_using [h₁, …]` (those facts only), `Proof/Framework/Omega.lean`.
* **Index bounds:** `xs[i]` proves `i < xs.length` with `get_elem_tactic`,
  whose core rules rewrite every hypothesis and run `omega`.
  `Proof/Framework/GetElem.lean` (which `Mem` imports) tries `decide`
  first, for literal indices; for any other index give the bound, `xs[i]'h`.
* **Satisfiability witnesses:** the regions of a concrete witness state are
  disjoint by `Region.disjoint_of_sep (by decide)`, not `bv_omega`.
* **`decide := true` in `simp`:** `simp (config := {decide := true})` runs
  `decide` on every closed proposition it visits: cheap for small facts
  (register equalities, small `Nat` comparisons, where simprocs measured
  slower), seconds per block when those facts evaluate expensive
  definitions. There, reduce them with simprocs (`reduceCtorEq`,
  `↓reduceIte`, `Nat.reduceLT`, `Nat.reduceEqDiff`, `and_self`, …) or
  discharge side conditions with `(disch := decide)`. Measure both;
  `ci/check_lean_speed.py` counts the uses per file
  (`ci/lean_speed_allowed.py`). `set_option simprocs false` turns off every
  simproc, even those listed in `simp only [...]`.
* **`assumption` among facts about states:** `assumption` tries every
  hypothesis at default transparency, unfolding states and registers before
  each failed match; use `with_reducible assumption`, or name the hypothesis
  (`ci/check_lean_speed.py` rejects a bare `assumption` after `<;>` or in
  `first`).
* **Numeral exponents:** `2 ^ 64` elaborates in time quadratic in the number
  of numeral exponents in a statement; `Proof/Framework/PowLit.lean`'s macro
  elaborates it as `2 ^ (64 : Nat)` (the same term). A module with numeral
  exponents imports it, directly or through `Framework/GetElem.lean`
  (`ci/check_lean_speed.py` checks it).
* **Failing unfolding:** `rfl`, `trivial`, `congr 1`, `exact` and `simpa` on
  goals about symbolic memory or hash values can unfold definitions (down
  to `BitVec` internals) for seconds before failing or succeeding. Close
  such goals with explicit lemmas (`congrArg`, `rw`), and try the tactic
  that works first rather than in `first | rfl | …`. For example, on
  `compress H (blockAt m p) = compress H (parseBlock f)` or
  `bytesAt m p n ++ [0x80] = xs ++ [0x80]`, use
  `refine congrArg (compress _) ?_` or `refine congrArg (· ++ [0x80]) ?_`,
  not `congr 1`, which first tries to unify both sides. A lemma proved
  `:= rfl` is one `simp` uses by definitional unfolding, which the kernel
  then repeats; where a profile shows that (e.g. `exec` of an instruction,
  `Proof/Blake2/X86_64/Avx/Round.lean`), prove it `:= (rfl)`. Keep the
  framework's `RegUpd` lemmas `rfl`: as propositional rewrites they measured
  slower.
* **Concrete data under `rfl`:** never close a goal holding a large concrete
  value (a key schedule read from memory, a table) by `rfl`, `decide` or
  `change`, nor split a case on an index (`rcases … with rfl | rfl`) in a
  context that holds one: the kernel may evaluate the value to compare the
  two sides (Blowfish's `step_run`: a minute in the kernel, after an
  unrelated upgrade of Lean). Prove the step once with the value a
  variable, and apply it (`fAcc_step`, `Proof/Blowfish/F.lean`), or
  `generalize` the value before `rfl`.
* **Tables of constants:** the kernel evaluates a table's whole length
  (seconds for a comb's tables) when it compares `8 * words.length` with
  another form of it, such as a `Region`'s `len` projection. Never unfold
  `Abi.constRegions` with `List.map_cons` or substitute a table's region
  into a goal: rewrite with `Abi.constRegions_cons`, `Abi.constRegions_nil`
  and `Sig.forall_mem_const_single` (`Proof/Framework/Sig.lean`, which
  `sig_pre` already uses), before `List.forall_mem_cons` or `forall_eq` can
  take the region apart. A definition the kernel unfolds (a witness's
  memory) states a table's size as a literal, not as `8 * words.length`. A
  table's shape (`<curve>Comb7_length`, `_rows`) is proven once, in
  `Proof/<Curve>/Comb7Shape.lean`, not by `decide` on each target.
* **Code without its literal:** `lit_decide` and `taint_decide` read the
  literal of code only if the module imports the module that materializes
  it, or a module that `public import`s it; otherwise the kernel builds the
  code again (seconds for unrolled code). Import the code's `Lit` module
  wherever its code is evaluated: registration files too, whose default
  `sp_safe` evaluates their code. `decide +kernel` reads no literal at all:
  use `lit_decide`. `python3 ci/check_lit_imports.py` lists the checks that
  evaluate code without a literal they could import (see the
  `lean-profiling` skill).
* **Unfolding recursive definitions:** `simp`/`dsimp` unfolding a recursive
  definition that uses a recursive call's result twice (`let r := f …;
  (… r.1, r.2)`) duplicates the call at every level. Evaluate it in one
  step with a `dsimproc` instead (`Arm.reduceClassify`,
  `Proof/Framework/Arm/Contract.lean`).
* **Unfolding a definition by `match` in `simp`:** `simp [f]` (and `dsimp`,
  `simp_all`, `simpa`) realizes `f`'s equation lemmas in the module, and
  those of its `match` (`f.match_N.eq_*`, `f.match_N.splitter`) under a
  private name, so no importer reuses them: every module that unfolds an
  ISA's `exec` this way carried about a megabyte of them in the build cache,
  and `simp` spent up to half a second realizing them. Unfold a model's
  function on an instruction given by its constructor with its `dsimproc`
  (`reduceExec`, `reduceVOpEval`, `reduceInstrDst`, …,
  `Proof/Framework/<ISA>/Reduce.lean`, built on `unfoldStep?` in
  `Proof/Framework/UnfoldStep.lean`), which unfolds by definitional
  reduction and realizes nothing; for a function without one, add it there.
  Rewrite with per-case lemmas proved `rfl` where there are a few cases
  (`Sig.bufs_array`, `Proof/Framework/Sig.lean`). A `dsimproc` reduces only
  the outer `match`, as an equation lemma does, but needs its argument to be
  a constructor: where a proof relies on `simp` unfolding a `match` it
  cannot reduce, keep the definition.
