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
  Evaluate each function's own code once: what holds of the functions it
  calls holds of it by composition (`NoSp.seq`, `NoSp.callP`, `NoSp.leaf`,
  `Proof/MlDsa/X86/KeyGen/NoSp.lean`), and its registration takes `spSafe`
  from that (`spSafe := NoSp.spSafe …`), not from the default, which
  evaluates the code with all it calls. A check of a wrapper by evaluation
  builds and walks the whole function under it again, in every wrapper and
  again in the registration: ML-DSA's on x86 cost 38 s so, in one
  registration file and the proofs of its entry points.
* **Matching on an instruction:** a function the kernel evaluates at every
  instruction matches on the instruction once. Each `match` on an ISA's
  `Instr` costs the kernel from 65 to 350 µs on x86-64, whose `Instr` has
  three hundred constructors (`isa.writesSp i`, a match around
  `Instr.dst`'s and a comparison of options, is the dearest): four of them
  were most of the 0.8 ms a plain instruction took in the residue analysis.
  Give what several matches computed by one, with the patterns of all of
  them, and prove it equal to the function it replaces by cases
  (`RTaint.stepFn1`, `stepFn1_eq`, `Proof/Framework/X86_64/`). The one
  match that is left still costs a third of a millisecond: Lean compiles
  it to a matcher, a function of the instruction and of the alternatives,
  and unfolding it builds a term of every case around the alternatives to
  keep one. `inline_match% f g …` (`Proof/Framework/Taint.lean`) is
  `f` as a `casesOn` whose cases are closed terms, with the matches of `f`
  and of the functions `g …` it applies to the instruction resolved in
  each (`stepKeepFnK`, `RTaint.stepFn1K`; equal to `f` by cases and
  `rfl`): the kernel evaluates such a function at every instruction it has
  not met before. So `spSafe`
  on x86 and x86-64 is checked with the ISA's `keepsSp`
  (`Proof/Framework/<ISA>/Taint.lean`), one match that compares the
  constructor's index, and `Code.all_of_spTest` (`SpTest`,
  `Proof/Framework/SpTest.lean`) gives the statement about `writesSp` from
  it: write `Code.all_of_spTest (by lit_decide)`, as `sp_safe` does, not
  `Code.all_of_allInstrs (by lit_decide)`, which tests `!isa.writesSp i`
  and takes twice as long for each instruction.
* **An analysis the kernel finds again:** the kernel evaluates a term when
  it is read, and remembers the value of every term it has evaluated, by
  the term. An analysis whose states are terms yet to be evaluated
  (`{ τ with regs := τ.regs.erase d }`, a term in the state before) never
  meets the same state twice; one whose states are evaluated finds again
  every step it has made from the same state, one lookup where a step is a
  hundred unfoldings, and code repeats itself far more than it looks
  (inlined field arithmetic: 85% of the steps of the residue analysis of
  brainpoolP512r1's ECDH on x86-64, whose check went from 23.8 s to 4.9 s).
  So a step function the kernel evaluates
  (`Proof/Framework/X86_64/Taint.lean` and `ResidueTaint.lean`,
  `Proof/Framework/Arm/Taint.lean`, `Proof/Framework/X86/Taint.lean` and
  `SseTaint.lean`):
  * gives a state that is evaluated: what it computed is forced before the
    state is built, in control flow, and the state built of the values
    (`Taint.forceT`: a set of registers by `RegSet.force`, which hands on
    a numeral, a `Bool` by `casesOn`; `forceList` for a list's first cell;
    on Arm a list that changed is evaluated through, `forceBases` and
    `forceSlots`, since it is a term in the whole taint before);
  * hands on the fields it does not change as the terms they were:
    destructure the state (`match τ with | ⟨rg, f, l, b, sl, lo, x⟩ =>`)
    rather than project or update it (`{ τ with … }` makes every field a
    term in `τ`), and decide whether a field changes before building the
    state (`keepBases`, `storeR`), not in the field: a field that is a term
    evaluating to the old field's term is unfolded again, with every such
    term below it, at each later read through a state the kernel has not
    read it through, since the kernel remembers the value of the term it
    was asked for and not of those it passed through (37 unfoldings of the
    slots for each store of that check);
  * never rebuilds a list it does not change (`killK`, a filter of the
    known bases at every instruction, cost 0.25 ms of CI for each base at
    each instruction): test first (`noBase b d`, which the kernel
    evaluates once for a list and a register);
  * leaves a numeral wider than 64 bits it changed as a term (x86's
    `Slots` masks, a bit for each byte of a region): the kernel's hash of
    a numeral is of its low 64 bits, so states that differ only above
    them have one hash, and a term looked up is compared with every term
    of its hash (with the masks evaluated, a check over an 8192-byte
    working space took 3.9 s for 3.4 s before and 1.2 s with them left as
    terms); only "unchanged" hands on the old term (`keepSlots`);
  * asks a list it walks at every step through a number that is a function
    of the list (`Taint.slotMask i l`, a bit for each byte a slot of the
    frame covers, and `Taint.slotKeys i l`, a bit for each slot): the
    kernel computes the number once for a list, and for a list with one
    more element from the number of the list without it (write it with
    `List.rec`, whose recursive result is that term), and a question is
    then a shift and a comparison where a walk is about 30 µs an element.
    The number answers the common cases and the walk remains for the
    others, in a function proven equal to the walk (`coveredQ_eq`,
    `slotThere_eq`, `allKeptQ_eq`), so nothing else changes; it is not a
    field of the state, which would be found again less often. SM4's
    residue checks walked 80,000 slots each for 4,500 instructions: 56 s
    to 36 s for the module;
  * keeps the model's helpers off the path of every step: one written for
    the proofs (`Int`, `Decidable` instances, the library's list
    functions) costs the kernel hundreds of unfoldings where the answer is
    usually known from a test it evaluates directly. A store computed the
    bytes it might write (`storeRange`) to remove from an empty list the
    pointers they overlap, half of its 1.7 ms: `mbQuiet` asks first whether
    there is anything to do (`mbStore_quiet`);
  * has the literal states of its hints written as its steps leave them
    (`Taint.T`'s `ToExpr` writes the sets' bits as raw numerals), so that
    the kernel finds again after a hint what it evaluated before it;
  * is proven equal to the function it replaces (`stepKeep_eq`,
    `stepF_eq`), which stays the one the soundness proofs are about.
  What is left is the instructions the kernel meets for the first time:
  see the next entry.
* **Code the kernel evaluates:** code built by functions (unrolled
  compression functions, and the functions calling them) is rebuilt by the
  kernel in every check that evaluates it (constant time, `spSafe`, …), in
  every module. Give it a literal: `materialize_code foo`
  (`Proof/Framework/Lit.lean`), in a `Lit.lean` next to its proofs, defines
  `foo.lit` and checks `foo.lit_eq` once; then `taint_decide` and
  `lit_decide` (not `decide +kernel`) evaluate the literal, and the
  registration file's `spSafe := Code.all_of_spTest (by lit_decide)`.
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
  taint domain (`Proof/Framework/<ISA>/TaintMono.lean`, `TaintSymMono.lean`,
  `SlotTaintMono.lean`, `SseTaintMono.lean`: each says which domains it is for).
  A summary costs one analysis of the callee, and a second pass over its
  instructions with `keeping` (the registers it does not write, which its
  callers still know after the call), so it pays from the third check that
  would analyse the callee: a hash's compression function, which `update`,
  `finalize`, HMAC and PBKDF2 all call, not a function with one or two
  callers. The callee's own constant time is the summary's
  (`Taint.exists_check_of_sumOk`). For a function its callers call
  (`.call name body`), summarize the call, named as they name it, not the
  body, which the hints would compare with the code at every call; a callee
  of a few hundred instructions does not pay, since what is left is a cost
  per call site (the four-word curves' field functions on RISC-V, measured
  and left). Within one
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
* **A hypothesis of many facts:** `obtain ⟨a₁, …, a₁₀₀⟩ := h` on a
  contract's evaluated precondition does a `cases` for every name, each in
  a context one fact larger: 4 to 12 s for the hundred facts of an RSA
  contract. `sig_split h` (`Proof/Framework/SigEval.lean`) asserts every
  conjunct in one step, and `rename_i` names them, in the conjunction's
  order: 0.3 s. The last conjunct keeps the name `h`; a conjunct that is
  itself a conjunction gets a name, and its own `obtain` or `sig_split`.
* **One tactic call that takes seconds:** most of a slow elaboration is
  often one call, and the build's profile names it (`lean-profiling`; a step
  of a theorem with a doc comment is recorded under the declaration before
  it). The causes found so far:
  * *Cases that each repeat the work.* `cases x <;> simp_all`, `interval_cases
    i <;> simp …`, or a block run again after `cases K <;> cases T`: `revert`
    what the cases need and close them by `decide`, prove the fact once for a
    general index, or run the block (and evaluate the precondition) once
    before the split and split only the goals that mention the value
    (`reduce_scan`, 512 `simp`s, over 20 s to 1 s; `qBase_ok`, `simp_all` in
    1024 cases, 13.9 s to 1.4 s).
  * *A discharger per side condition.* `simp (disch := omega)` runs `omega`
    in the whole context for every condition of every rewrite. Closed
    conditions take `(disch := decide)`; others, their facts proved once and
    given to a plain `simp only`, or `(disch := omega_using [h₁, h₂])`
    (`prepWord0_ok`, 1165 `omega`s).
  * *`omega` on what is not linear.* A fact holding `BitVec.toNat 0`, a nest
    of `2 ^ 64 * (…)` or of `% 2 ^ 32` sums costs each `omega_arith` seconds:
    rewrite the fact first, or prove the nonlinear pieces once as named facts
    and give only those (`omega_using`). Plain `omega` in a context of a
    hundred facts is several times `omega_arith`.
  * *An alternative that fails slowly.* In `first | A | B` and in
    `repeat' apply And.intro` followed by `all_goals first | …`, a failing
    `exact`, `refine … (lemma _ (by decide))`, `trivial` or `rfl` may unify
    for seconds before it fails. Put the one that works first, make the
    other fail fast (`with_reducible exact h`, `exact rfl`), or expand the
    facts once and close every conjunct with one `simp only`.
  * *An implicit argument left to unification.* `rw [wa_shift h]`, where `h`
    determines a structure only through one of its fields, took 11.6 s to
    find it: give it, even in part (`(τ' := ⟨_, _, _, _, τ.room - 8, _, …⟩)`).
  * *A term elaborated before its implicit arguments are known.* `exact
    lemma h₁ h₂`, `cutThen_trace check …` or `bytesAt_frame …` whose implicit
    region or state appears in the goal only under a projection is unified
    by unfolding (`bytesAt`, `taint.check`, a key's status): name the
    arguments (`(r := ⟨addr, len⟩)`, `(s := s₂)`), or state the fact with
    `have` and `exact` it. The same for `h ▸ e`, `congr n` and
    `show a = b from rfl` between two states' memories or two programs:
    `rw [h]`, `congrArg` with the function written out, `kernel_rfl`.
  * *Small goals by a large tactic.* An inclusion of literal register lists
    by `simp [regs]` (3.5 s), a propositional case analysis by `omega`,
    fifty side goals over literal lists by default `simp`: `decide`. Thirty
    nested `max` by `omega_arith` (3.7 s): `Nat.max_le` in a `simp only`. A
    `fun | [x₁, …, x₁₈], h => …` on a computed list refutes every other
    length once per pattern: take the length as a numeral in a lemma.
  * *Reads through writes after the fact.* With `RegUpd.gpr_write` and
    `ite_true, ite_false` as ordinary rewrites, `simp` simplifies the value
    of every write a read passes: `↓RegUpd.gpr_write` and `↓reduceIte`
    rewrite the read first and never visit the discarded branch. A shared
    run tactic without `↓reduceIte` pays this in every block: `ffrun`'s time
    doubled with each instruction that has an operand to evaluate (3.6 s for
    ten), and its 125 modules took 141 s; with it, 98 s. A run tactic that
    unfolds the writes themselves (`State.write`) re-simplifies every
    earlier register function at each instruction: keep them folded and
    read through them (`crunw`, `MlKem1024/RISCV64/`).
  * *Interpreted arithmetic.* Mathlib's `nlinarith` multiplies every pair of
    facts, in the interpreter: 5 to 11 s for `2 * x ≤ x * 2 ^ 63`. State the
    products as facts and use `omega_using` (which takes `2 ^ k` for an
    atom), or `linarith` where the products are hypotheses already.
* **A module slow in many small places:** when no declaration stands out,
  one idiom is usually repeated through the file. The ones found so far:
  * *Facts `omega_arith` collects that no goal needs.* One alignment fact
    (`x % 8 = 0`) among the hypotheses made each call three to four times
    slower (`TComb`): state the conjuncts the goals use (`lay_lin`), not the
    whole layout. An `omega_using` list that carries six separation
    disjunctions where one is needed has `omega` split on each (`RdDiv`:
    479 facts removed from 86 calls).
  * *Multi-word values unfolded into their words.* `omega` over 8 to 14
    atoms with coefficients up to `2 ^ 256`: keep each value one atom and
    state the arithmetic about the values (`P256Field/Fn`), or state each
    word's sum and carry once and close with one `omega` (`sub3w_ok`).
  * *`grind` on a ring identity among a hundred hypotheses.* Move the
    identity to a private lemma whose only hypotheses are the equations it
    uses, and `exact` it (`GenWide/Sqr`, `SqrtLoop`).
  * *An alignment closed by `dsimp`.* `(… .syms name).toNat % 64 = 0` on a
    term with free variables has the kernel take the remainder in unary:
    `rw [show … .syms name = <address> from rfl]; decide` (`SignEntryTiming`,
    `Message`: 3 s to 0.2 s each).
  * *A pattern-matching `fun` on a hypothesis with a very large type*
    (`fun σ s ⟨⟨⟨h, x⟩, _⟩, z⟩ => …`) compiles a matcher each time, up to
    1 s: take the hypothesis and project, or `obtain` on the next line.
  * *A macro every proof calls.* `oomega` took a 23-fact conjunction apart
    with `obtain` at each of its 225 uses: `have := offsO; omega_arith`
    reads it as it is.
  * *Alternatives that fail at every node.* A `repeat' (first | …)` over a
    tree of code that begins with the callees' lemmas, each by `exact`,
    elaborates every one that does not fit at every node, and an `exact`
    that does not fit looks for a coercion first (about 1,300 in one
    theorem): closed code and code that is a `seq`, `ite` or `call` as it
    stands come first, and the lemmas are applied (`s16_xd`), or each is
    tried only where the code's head is its function (`code_head`,
    `MlKem/AArch64/CallWipe`).
  * *Every hypothesis simplified once per goal.* `sig_and_intros` and then
    `all_goals simp only […] at *`: simplify once, before the goals are
    split. `split <;> split <;> omega_arith` among a hundred hypotheses,
    whose discharger scans them for every `if`: a lemma about the `if`s
    (`ite3_lt`), applied.
  * *Two postconditions that match on the same computation.* Where the
    kernel compares a `match decrypt … with` with a term that only unfolds
    to it, it evaluates `decrypt` on symbolic bytes (52,000 unfolds each
    time): match on a variable (`CorePostOf`) and unfold the contract's
    postcondition by `rw`.
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
  slower. A lemma whose right side is one of its arguments
  (`XBinOp.eval .movdqa a b = b`) is the worst case: where `b` is another
  application of the same function, the kernel compares their arguments,
  fails, and unfolds both (`vbfly_ok`, 4.5 s of 4.6).
  The kernel compares two applications of one function by their arguments
  first, and unfolds the function only when that fails, which for two
  machine states or two memories is after evaluating what it can of them.
  So `rfl` is slow on `f t … = f s …` whatever `f` is: an induction's base
  case (`keyPartsBytes t base [] = keyPartsBytes s base []`: rewrite both
  sides with the equation for `[]`), a frame fact of a state `simp` left
  half evaluated (`t.rd = s.rd`: give `simp` every `RegUpd` lemma of the
  field, `rd_arithFlags` with `rd_setReg`, so that the field is `s.rd`
  itself), a function updated at other points (`upd (upd f 16 a) 19 b 3 =
  f 3`: `ite_eq_right (by decide)` for each update). Each took 2 to 3 s.
* **An equality the elaborator finds by evaluating:** `rfl`, and an
  `exact h` or `fun _ h => h` whose type differs from the goal's, have the
  elaborator unify the two, and it may unfold the wrong thing first.
  `(Serial.coreSpec .encrypt).cipher k = Spec.Sm4.cipher k` differs by a
  projection of a structure and a `match` on the direction, but the
  elaborator unfolded the cipher on both sides and evaluated the
  `Vector.ofFn` of its sixteen input bytes, 3 s a time and several times a
  proof: fifteen proofs of one to three lines (SM4 and SEED's modes on
  PPC64LE and RISC-V) took 353 s between them, and the kernel no time at
  all. State such an equality once, proved by unfolding exactly what
  differs (`simp only [Serial.coreSpec, dirCipher]`) or by `kernel_rfl`, and
  rewrite a hypothesis with it before `exact`
  (`fun _ h => by simp only [cipher_ser] at h; exact h`). A proof of a few
  lines that elaborates for seconds, with no kernel time, is this. So is
  `hx ▸ h.x` between facts about two states' memory, which first tries the
  two as they are (`by rw [hx]; exact h.x`: Ecdsa's `PtOk.of_eq` on RISC-V,
  86 s in eighteen copies), and a lemma applied with an implicit argument
  that only the expected type determines, which is compared with it, in
  vain, before the arguments are elaborated: name the argument
  (`digestFrame (SH := ok.SH) (bytes := …)`).
* **A proposition that is a `match` on a computed value:** the elaborator
  reduces a term's type to weak head normal form whenever it elaborates the
  term, to see whether it is a function, and so does the linter. For
  `openOut (decryptWith …) …`, a definition by `match` on the result of a
  decryption, that evaluates the decryption as far as its first comparison
  of tags: AES on symbolic bytes, 1.4 s each time `hp` is named. AES-GCM-SIV's
  `open` on RISC-V and PPC64LE spent 91 s there. Make such a definition
  `@[irreducible]` and unfold it by name where a proof takes it apart; where
  a hypothesis is itself such a `match`, generalize what it matches on
  before using it (`generalize decryptWith _ _ _ _ _ _ = res at hp ⊢`).
* **`generalize` does not hide a value from the kernel:** the proof term
  `generalize` (and `revert`) builds is an application of the new goal's
  proof to the value, which `instantiateMVars` beta-reduces, so the kernel
  checks every step after it with the value substituted back. A step the
  kernel checks by evaluation (`sig_pre`'s `sig_reduce`, `change`, `rfl`)
  then evaluates the value: each PPC64LE comb's satisfiability proof built
  its whole table this way (about 3 GB). Abstract it where the term keeps
  a binder: `obtain ⟨W, eW⟩ : ∃ W, words = W := ⟨_, rfl⟩` and
  `rw [eW] at …` (the `Exists` case's lambda), or a lemma over any `W`.
* **Concrete data under `rfl`:** never close a goal holding a large concrete
  value (a key schedule read from memory, a table) by `rfl`, `decide` or
  `change`, nor split a case on an index (`rcases … with rfl | rfl`) in a
  context that holds one: the kernel may evaluate the value to compare the
  two sides (Blowfish's `step_run`: a minute in the kernel, after an
  unrelated upgrade of Lean). Prove the step once with the value a
  variable, and apply it (`fAcc_step`, `Proof/Blowfish/F.lean`), or
  abstract the value with `obtain` (not `generalize`: see above).
* **Arithmetic the kernel evaluates is in a closed term:** the kernel adds,
  multiplies, shifts and compares numerals as numerals only in a term with
  no free variable in it (a state `s`, an opaque memory `m`, a hypothesis's
  variable), even one in a branch it never takes. With one, it unfolds
  `Nat.add`, `Nat.mul` and `Nat.shiftLeft` by their recursion: a byte
  shifted left by 16 is 65,536 steps. `prepared_sign_sat`
  (`Proof/MlDsa/X86/PreparedKey.lean`) read five argument words from
  `above satMemE m`, below the address where `m` begins: 18 s. Rewrite to a
  closed term first, with a lemma (`above_readW`), and evaluate that
  (`decide +kernel`, `kernel_rfl`). The same is behind a `simp` that unfolds
  `Mem.readW` under `… + 213056` on a state's registers, and behind most
  proofs whose kernel profile is `Nat.add` or `Nat.mul` by the million.
* **A checker's environment is data, not a function:** a reflective
  checker that keeps its registers as `fun q => if q = r then v else f q`,
  one function for every write, has the kernel follow the whole chain again
  for every read: it remembers the values of terms it was asked for, and a
  read part of the way down a chain is not one. As a list with a
  register's value at its index, written with `List.set`, each list is
  evaluated once. `Sha3.AArch64.Scalar`'s symbolic run of the 25 lanes took
  29.5 s as functions and 2 s as a list (`KFile`, `symRun_regs`,
  `Proof/Sha3/AArch64/Scalar/Reflect.lean`): keep the function, which the
  proofs about the checker read easily, and prove it equal to the list's.
  A fold that filters a list at every step has the same shape: the kernel
  evaluates lazily, so after 15,000 instructions the list is a filter of a
  filter of the first, and each element is forced through all of them.
  Rebuild the list at each step (`forceL`, `checkK`, `keepsK_eq` in
  `Proof/Bignum/AArch64/KeepLanes.lean`: half the time).
* **Tables of constants:** the kernel evaluates a table's whole length
  (seconds for a comb's tables) when it compares `8 * words.length` with
  another form of it, such as a `Region`'s `len` projection. Never unfold
  `Abi.constRegions` with `List.map_cons`, name it among the definitions
  `sig_pre` unfolds (give it the two lemmas' names instead: each Arm comb's
  satisfiability proof spent 5 to 13 s in the kernel on that one name), or
  substitute a table's region into a goal: rewrite with
  `Abi.constRegions_cons`, `Abi.constRegions_nil`
  and `Sig.forall_mem_const_single` (`Proof/Framework/Sig.lean`, which
  `sig_pre` already uses), before `List.forall_mem_cons` or `forall_eq` can
  take the region apart. State a table's own facts with the
  `ConstsOk` lemmas (`fit`, `mem_rd`, `disjoint_wr`), whose words are a
  variable, not as `h.2.2.1 _ (List.mem_map_of_mem …)` at a concrete table,
  whose `8 * (name, words).2.length` the kernel compares with
  `8 * words.length` by evaluating both. A definition the kernel unfolds (a witness's
  memory) states a table's size as a literal, not as `8 * words.length`. A
  table's shape (`<curve>Comb7_length`, `_rows`) is proven once, in
  `Proof/<Curve>/Comb7Shape.lean`, not by `decide` on each target.
* **Signatures with stack arguments:** give `sig_pre`, `sig_post` and
  `sig_pub` the definitions `List.range` and `List.range.loop` for a function
  some of whose arguments are on the stack, not a lemma for the stack
  arguments' list (`stackArgs_sixteen`). The calling conventions state those
  arguments as `(List.range n).map (stackArg s)`; unless `sig_reduce` may
  unfold `List.range` it stops there, with `Sig.bufs`, `Sig.alignedBufs` and
  `Curry.apply` unfolded over the arguments in registers only. The kernel
  checks that half-evaluated goal against the contract by unfolding both,
  out of step, and where their heads agree it compares the arguments at the
  same position: a register with a stack argument, or two different stack
  arguments, which are not equal, as it finds only after evaluating their
  memory reads as far as it can (10 to 40 s for an RSA contract with twenty
  arguments). With `List.range` unfolded the evaluation finishes in that one
  step, and what the kernel checks is the contract's own evaluation. The
  lemmas that tidied the half-evaluated goal afterwards then have nothing to
  do (a `simp only` after it, a trailing `-` in a pattern).
* **Code without its literal:** `lit_decide` and `taint_decide` read the
  literal of code only if the module imports the module that materializes
  it, or a module that `public import`s it; otherwise the kernel builds the
  code again (seconds for unrolled code). Import the code's `Lit` module
  wherever its code is evaluated: registration files too, whose default
  `sp_safe` evaluates their code. `decide +kernel` reads no literal at all:
  use `lit_decide`. `python3 ci/lit_imports.py` lists the checks that
  evaluate code without a literal they could import (see the
  `lean-profiling` skill).
* **Equations between code:** prove that two programs, or two lists of
  programs, are the same with `kernel_rfl`, not `decide +kernel`. `decide`
  evaluates both sides to their last operand and compares them with
  `DecidableEq`, whatever they share; the kernel's own comparison stops at a
  subterm that is the same on both sides (a program both name) without
  evaluating it. `Proof/Bignum/PPC64LE/CrtPinsB.lean` says ten times that a
  prefix of the CRT's flattened code is a program written from the same
  parts (`WP.of_flat`): 42 s by `decide +kernel`, 1.4 s by `kernel_rfl`.
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
