import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
import VerifiedGarbage.Proof.Ed448.X86.BaseLit
import VerifiedGarbage.Proof.Framework.X86.TaintErase
import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Constant time of Ed448's base-point multiplication and verification on x86 (32-bit), after their entry

Base-point multiplication and verification's equation run much of the same
field arithmetic (`Impl/Ed448/X86/ScalarBase.lean`): the doublings and
additions of the loops over the bits, and most of X448's addition chain,
which the inversion and the square root share. The kernel analyses the same
code from the same taint once within one check, so the code after the entry
block of both functions is analysed here in one check (`rest_ct`).

Their taints differ on entry (the working space is writable region 1 of one
and region 0 of the other, and their arguments differ), so each function's
entry block, which loads the pointers, is analysed on its own
(`relCT_split`), and the analysis then forgets all it knows about memory but
the arguments' first 12 bytes (`fieldτ`): the rest of both functions needs
nothing else public, as every store and load is at a public register plus a
constant, and the only loads that must be public are of the arguments.

Verification's loop decoding `R` and `A` loads the pointer to the point it
decodes from the working space, which the analysis does not know public: its
first block (`vbodyA`, ending with that load) is analysed from `fieldτ` to a
taint public but for `esi` (`weakOkEsi`), and the proof of `Verified` shows
`esi` the same in both runs (`agree_fieldτ_esi`); the rest of an iteration,
the block before the loop and the code after it are analysed from `fieldτ`.

Knowing no region, the analysis of the rest does not read the displacements
of its memory operands (but at `esp`) or its immediates
(`Framework/X86/TaintErase.lean`): the code without them (`Code.erase`), in
which the field arithmetic on different slots is the same code, is analysed
instead, and the kernel analyses each operation once.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86

/-- What the code after the entry needs public: the stack pointer, the loop
counter, the working space, and the arguments' first 12 bytes. -/
def fieldτ : VG.X86.Taint.T := { regs := .ofList [.esp, .esi, .edi], flags := false, argLen := 12 }

/-- A taint with at least what `fieldτ` has public, and no stack frames. -/
def weakOk (τ : VG.X86.Taint.T) : Bool :=
  fieldτ.regs.subset τ.regs && τ.stk == [] && Nat.ble 12 τ.argLen

theorem wf_fieldτ {τ : VG.X86.Taint.T} {s : State} (hstk : τ.stk = []) (hl : 12 ≤ τ.argLen)
    (h : VG.X86.Taint.Wf τ s) : VG.X86.Taint.Wf fieldτ s := by
  obtain ⟨a1, a2⟩ := h.args (by omega)
  rw [hstk] at a1 a2
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨?_, fun r hr => ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, ?_, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0)⟩
  · change (s.gpr .esp).toNat + 0 + 12 ≤ 2 ^ 32
    simp only [VG.X86.Taint.depth] at a1
    omega
  · exact (a2 r hr).sub_left (Region.sub_prefix hl)
  · change (s.gpr .esp).toNat + 0 < 2 ^ 32
    have := (s.gpr .esp).isLt
    omega

/-- Two states that agree on what `τ` says is public agree on what `fieldτ`
says, if `weakOk τ`. -/
theorem agree_fieldτ {τ : VG.X86.Taint.T} {s t : State} (hw : weakOk τ = true)
    (h : VG.X86.Taint.Agree τ s t) : VG.X86.Taint.Agree fieldτ s t := by
  simp only [weakOk, Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨hr, hstk⟩, hl⟩ := hw
  have hl := Nat.le_of_ble_eq_true hl
  refine ⟨⟨fun r hr' => h.rf.1 r (RegSet.mem_of_subset hr hr'), fun h => absurd h (by decide)⟩,
    fun h => absurd rfl h, wf_fieldτ hstk hl h.wf₁, wf_fieldτ hstk hl h.wf₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => h.sp (by omega), fun k h4 hk => ?_⟩
  have := h.argMem k h4 (by change k < 12 at hk; omega)
  rw [hstk] at this
  exact this

/-- The entry block of code that starts with one, and the rest. -/
def head : Prog isa → Prog isa
  | .seq a _ => a
  | c => c

def tail : Prog isa → Prog isa
  | .seq _ b => b
  | _ => .block []

/-- A taint with what `fieldτ` has public but `esi`, and no stack frames. -/
def weakOkEsi (τ : VG.X86.Taint.T) : Bool :=
  (RegSet.ofList [.esp, .edi]).subset τ.regs && τ.stk == [] && Nat.ble 12 τ.argLen

/-- Two states that agree on what `τ` says is public, and on `esi`, agree on
what `fieldτ` says, if `weakOkEsi τ`. -/
theorem agree_fieldτ_esi {τ : VG.X86.Taint.T} {s t : State} (hw : weakOkEsi τ = true)
    (h : VG.X86.Taint.Agree τ s t) (he : s.gpr .esi = t.gpr .esi) : VG.X86.Taint.Agree fieldτ s t := by
  simp only [weakOkEsi, Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨hr, hstk⟩, hl⟩ := hw
  have hl := Nat.le_of_ble_eq_true hl
  refine ⟨⟨fun r hr' => ?_, fun h => absurd h (by decide)⟩,
    fun h => absurd rfl h, wf_fieldτ hstk hl h.wf₁, wf_fieldτ hstk hl h.wf₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => h.sp (by omega), fun k h4 hk => ?_⟩
  · simp only [fieldτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact h.rf.1 _ (RegSet.mem_of_subset hr (by simp only [RegSet.mem_ofList]; decide))
    · exact he
    · exact h.rf.1 _ (RegSet.mem_of_subset hr (by simp only [RegSet.mem_ofList]; decide))
  · have := h.argMem k h4 (by change k < 12 at hk; omega)
    rw [hstk] at this
    exact this

/-- Constant time of the entry block `head c` from `τ`, ending with at least
what `fieldτ` has public, and of the rest from `fieldτ`. -/
theorem relCT_split {P : State → State → Prop} {c : Prog isa} (hc : c = .seq (head c) (tail c))
    (τ : VG.X86.Taint.T) (hp : ∀ s t, P s t → VG.X86.Taint.Agree τ s t)
    {h₁ : VG.Taint.Hint VG.X86.Taint.T} (c₁ : (taint.check τ (head c) h₁).any weakOk = true)
    (c₂ : ∃ h₂, (taint.check fieldτ (tail c) h₂).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, c₂⟩ := c₂
  rw [hc]
  refine RelCT.seq ?_ (RelCT.taint (A := taint) fieldτ (fun _ _ h => h) c₂)
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hw⟩ : ∃ τ', taint.check τ (head c) h₁ = some τ' ∧ weakOk τ' = true := by
    cases e : taint.check τ (head c) h₁ with
    | none => rw [e] at c₁; cases c₁
    | some τ' => rw [e] at c₁; exact ⟨τ', rfl, c₁⟩
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hP) e₁ e₂
  exact ⟨ht, agree_fieldτ hw ha⟩

open Lean Meta Elab Tactic in
/-- `taint_decide` for a goal with several `Taint.check`s: computes the hint
of each (`Taint.hintOf`), and has the kernel evaluate the goal once, so that
it analyses code the checks share once. -/
elab "taint_decide_all" : tactic => do
  -- The goal of the equation; the others are the hints it assigns.
  let some g := (← getGoals).getLast? | throwError "taint_decide_all: no goals"
  for _ in [0:16] do
    let ty ← instantiateMVars (← g.getType)
    let some chk := ty.find? fun e => e.isAppOfArity ``Taint.check 5 && (e.getArg! 4).isMVar
      | break
    let args := chk.getAppArgs
    let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
    let tT ← whnfD (mkApp2 (mkConst ``Taint.T) m a)
    let hty := mkApp (mkConst ``Taint.Hint) tT
    let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) hty)
    let hint := mkApp4 (mkConst ``Taint.hintOf) m a τ c
    let hv ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) hty inst hint)
    h.mvarId!.assign hv
  setGoals [g]
  evalTactic (← `(tactic| lit_decide))

/-- The code after the entry of both functions, without its displacements and
immediates (`Code.erase`): the field arithmetic on different slots is then
the same code. Verification's is in pieces: the block before the decoding
loop, the two parts of an iteration, and the code after the loop. -/
def verifyInit : Prog isa := Code.erase (.block Impl.Ed448.X86.vdecodeInit)
def verifyBodyA : Prog isa := Code.erase (.block Impl.Ed448.X86.vbodyA)
def verifyBodyB : Prog isa := Code.erase (.seq (Impl.Ed448.X86.decode 6 7) (.block Impl.Ed448.X86.vnext))
def verifyRest : Prog isa := Code.erase Impl.Ed448.X86.vafter
def baseRest : Prog isa := Code.erase (tail Impl.Ed448.X86.scalarBase)

materialize_code verifyInit
materialize_code verifyBodyA
materialize_code verifyBodyB
materialize_code verifyRest
materialize_code baseRest

/-- The code after the entry of both functions, analysed from `fieldτ` in one
check. -/
theorem rest_ct : ∃ h₁ h₂ h₃ h₄ h₅,
    (Taint.hintNoBases h₁ && (taint.check fieldτ verifyInit h₁).any weakOk &&
    Taint.hintNoBases h₂ && (taint.check fieldτ verifyBodyA h₂).any weakOkEsi &&
    Taint.hintNoBases h₃ && (taint.check fieldτ verifyBodyB h₃).any weakOk &&
    Taint.hintNoBases h₄ && (taint.check fieldτ verifyRest h₄).isSome &&
    Taint.hintNoBases h₅ && (taint.check fieldτ baseRest h₅).isSome) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  taint_decide_all

/-- A check of erased code is the check of the code. -/
theorem of_erase {c : Prog isa} {h : VG.Taint.Hint VG.X86.Taint.T} (hh : Taint.hintNoBases h = true)
    {p : VG.X86.Taint.T → Bool} (hc : (taint.check fieldτ (Code.erase c) h).any p = true) :
    ∃ τ', taint.check fieldτ c h = some τ' ∧ p τ' = true := by
  rw [Taint.check_erase _ _ _ rfl hh] at hc
  cases e : taint.check fieldτ c h with
  | none => rw [e] at hc; cases hc
  | some τ' => rw [e] at hc; exact ⟨τ', rfl, hc⟩

theorem verifyInit_ct : ∃ h τ', taint.check fieldτ (.block Impl.Ed448.X86.vdecodeInit) h = some τ' ∧
    weakOk τ' = true := by
  obtain ⟨h₁, _, _, _, _, h⟩ := rest_ct
  simp only [Bool.and_eq_true] at h
  exact ⟨h₁, of_erase h.1.1.1.1.1.1.1.1.1 h.1.1.1.1.1.1.1.1.2⟩

theorem verifyBodyA_ct : ∃ h τ', taint.check fieldτ (.block Impl.Ed448.X86.vbodyA) h = some τ' ∧
    weakOkEsi τ' = true := by
  obtain ⟨_, h₂, _, _, _, h⟩ := rest_ct
  simp only [Bool.and_eq_true] at h
  exact ⟨h₂, of_erase h.1.1.1.1.1.1.1.2 h.1.1.1.1.1.1.2⟩

theorem verifyBodyB_ct : ∃ h τ', taint.check fieldτ (.seq (Impl.Ed448.X86.decode 6 7)
    (.block Impl.Ed448.X86.vnext)) h = some τ' ∧ weakOk τ' = true := by
  obtain ⟨_, _, h₃, _, _, h⟩ := rest_ct
  simp only [Bool.and_eq_true] at h
  exact ⟨h₃, of_erase h.1.1.1.1.1.2 h.1.1.1.1.2⟩

theorem verifyRest_ct : ∃ h, (taint.check fieldτ Impl.Ed448.X86.vafter h).isSome = true := by
  obtain ⟨_, _, _, h₄, _, h⟩ := rest_ct
  simp only [Bool.and_eq_true] at h
  refine ⟨h₄, ?_⟩
  rw [← Taint.check_erase _ _ _ rfl h.1.1.1.2]
  exact h.1.1.2

theorem baseRest_ct : ∃ h, (taint.check fieldτ (tail Impl.Ed448.X86.scalarBase) h).isSome = true := by
  obtain ⟨_, _, _, _, h₅, h⟩ := rest_ct
  simp only [Bool.and_eq_true] at h
  refine ⟨h₅, ?_⟩
  rw [← Taint.check_erase _ _ _ rfl h.1.2]
  exact h.2

end VG.Proof.Ed448.X86
