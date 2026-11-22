module

public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Mmx

/-!
# x86 SIMD: constant-time analysis

This extends the checked scalar analysis without changing its domain or
agreement relation. SIMD values are secret, and register-only SIMD operations
cannot change any general-purpose register, flag or memory. Loads must use
public addresses; stores use the existing checked secret-store rule for sixteen
bytes (eight for `movq`). MMX values are secret too, as are the MMX
instructions' memory sources' contents: their addresses must be public. A
load of a table its instruction carries (`movdquTbl`, `movqTbl`) is observed
as its offset in the table, a constant, whatever its base register holds.
-/

@[expose] public section

namespace VG.X86.SseTaint
open VG.X86.Taint

/-- SIMD operations alter only SIMD registers, which the analysis does not track. -/
theorem XOp.exec_eq (op : XOp) (s : State) :
    op.exec s = { s with xmm := (op.exec s).xmm } := by
  cases op <;> rfl

theorem agree_withXmm {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (x₁ x₂ : XReg → BitVec 128) :
    Agree τ { s₁ with xmm := x₁ } { s₂ with xmm := x₂ } :=
  ha.keep ha.rf rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ha.wf₁.bases ha.wf₂.bases

theorem agree_withMm {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (m₁ m₂ : MReg → BitVec 64) (x₁ x₂ : XReg → BitVec 128) :
    Agree τ { s₁ with mm := m₁, xmm := x₁ } { s₂ with mm := m₂, xmm := x₂ } :=
  ha.keep ha.rf rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ha.wf₁.bases ha.wf₂.bases

/-- An MMX instruction's memory source, if any, has a public address. -/
def mopOk (τ : T) : MOp → Bool
  | .bin _ _ (.mem m) | .movq _ (.mem m) => memPub τ m
  | _ => true

/-- Scalar instructions retain the existing transfer function. -/
def step (τ : T) : Instr → Option T
  | .movdquLoad _ m => if memPub τ m then some τ else none
  | .movdquStore m _ => storeStepK τ m 16 false []
  | .movqLoad _ m => if memPub τ m then some τ else none
  | .movqStore m _ => storeStepK τ m 8 false []
  -- A table an instruction carries is observed as its offset, a constant.
  | .xop _ | .pmuludq .. | .movdquTbl .. | .movqTbl .. => some τ
  | .mop op => if mopOk τ op then some τ else none
  | .mmxStore m _ => storeStepK τ m 8 false []
  | i => Taint.stepK τ i

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (hs : step τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | mov | store | alu | shift | bswap | movzx8 | store8 | mul | symPush | push | pop | alloc | free | callr =>
    simp only [step] at hs
    exact Taint.step_sound ha (Taint.stepK_eq ▸ hs) e₁ e₂
  | movdquLoad d m =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hm; cases hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, -, rfl⟩ := e₁; obtain ⟨v₂, -, rfl⟩ := e₂
    exact ⟨by simp only [addrs, ha.ea hm], agree_withXmm ha _ _⟩
  | movdquStore m r =>
    simp only [step, storeStepK_eq, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hm; cases hs
    refine ⟨by simp only [addrs, ha.ea hm], ?_⟩
    simp only [exec, State.store128] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    rename_i h₁ h₂
    cases e₁; cases e₂
    exact ha.store (n := 16) hm (by decide) (fun hp => by cases hp) h₁ h₂
      (fun _ h => (List.not_mem_nil h).elim) (fun _ h => (List.not_mem_nil h).elim)
  | movqLoad d m =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hm; cases hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, -, rfl⟩ := e₁; obtain ⟨v₂, -, rfl⟩ := e₂
    exact ⟨by simp only [addrs, ha.ea hm], agree_withXmm ha _ _⟩
  | movqStore m r =>
    simp only [step, storeStepK_eq, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hm; cases hs
    refine ⟨by simp only [addrs, ha.ea hm], ?_⟩
    simp only [exec, State.store64] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    rename_i h₁ h₂
    cases e₁; cases e₂
    exact ha.store (n := 8) hm (by decide) (fun hp => by cases hp) h₁ h₂
      (fun _ h => (List.not_mem_nil h).elim) (fun _ h => (List.not_mem_nil h).elim)
  | mop op =>
    simp only [step] at hs
    split at hs <;> [rename_i hm; cases hs]
    cases hs
    simp only [exec] at e₁ e₂
    refine ⟨?_, by rw [MOp.exec_eq e₁, MOp.exec_eq e₂]; exact agree_withMm ha _ _ _ _⟩
    cases op with
    | bin o d src | movq d src =>
      cases src with
      | reg _ => rfl
      | mem m => simp only [mopOk] at hm; simp only [addrs, MOp.addrs, MSrc.addrs, ha.ea hm]
    | _ => rfl
  | mmxStore m r =>
    simp only [step, storeStepK_eq, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hm; cases hs
    refine ⟨by simp only [addrs, ha.ea hm], ?_⟩
    simp only [exec, State.store64] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    rename_i _ _ h₁ h₂
    cases e₁; cases e₂
    exact ha.store (n := 8) hm (by decide) (fun hp => by cases hp) h₁ h₂
      (fun _ h => (List.not_mem_nil h).elim) (fun _ h => (List.not_mem_nil h).elim)
  | mmxEnter | emms | mcdtEnter | mcdtLeave =>
    simp only [step, Taint.stepK_eq, Taint.step, reduceCtorEq] at hs
  | pmuludq d r =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, agree_withXmm ha _ _⟩
  | xop op =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    rw [XOp.exec_eq op s₁, XOp.exec_eq op s₂]
    exact ⟨rfl, agree_withXmm ha _ _⟩
  | movdquTbl d m name ws | movqTbl d m name ws =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, agree_withXmm ha _ _⟩

/-! ### Steps the kernel finds again

`stepKeep` is `step` as the kernel evaluates it (`Taint.stepKeep`): its
taints are evaluated, and their bases, slots and base-address words are the
terms they were when the instruction does not change them. Its stores keep
the slots that already say what the store makes of them
(`Taint.storeStepKD`): the same public bytes and the same taint otherwise
(`stepKeep_spec`). -/

/-- `step`, classifying the instruction before the taint it is given
(`Taint.stepKDFn`), with `Taint.stepKeepFn` for the scalar instructions. -/
def stepKeepFn : Instr → Taint.Step
  | .movdquLoad _ m | .movqLoad _ m => ⟨fun τ => bif pub τ m.base then some τ else none⟩
  | .movdquStore m _ => ⟨fun τ => storeKeep τ m 16 false []⟩
  | .movqStore m _ | .mmxStore m _ => ⟨fun τ => storeKeep τ m 8 false []⟩
  | .xop _ | .pmuludq .. | .movdquTbl .. | .movqTbl .. => ⟨some⟩
  | .mop op => ⟨fun τ => bif mopOk τ op then some τ else none⟩
  | i => Taint.stepKeepFn i

/-- `stepKeepFn`, with its cases closed (`inline_match%`). -/
def stepKeepFnK : Instr → Taint.Step :=
  inline_match% VG.X86.SseTaint.stepKeepFn VG.X86.Taint.stepKeepFn VG.X86.Taint.stepKDFn

theorem stepKeepFnK_eq (i : Instr) : stepKeepFnK i = stepKeepFn i := by
  cases i <;> rfl

/-- `step`, as the kernel evaluates it (`stepKeep_spec`). -/
def stepKeep (τ : T) (i : Instr) : Option T :=
  match (stepKeepFnK i).run τ with
  | some τ' => forceT τ' some
  | none => none

theorem stepKeep_run (τ : T) (i : Instr) : stepKeep τ i = (stepKeepFn i).run τ := by
  unfold stepKeep
  rw [stepKeepFnK_eq]
  cases (stepKeepFn i).run τ with
  | none => rfl
  | some τ' => exact forceT_eq τ' some

theorem stepKeep_spec (τ : T) (i : Instr) :
    (stepKeep τ i = none ∧ step τ i = none) ∨ ∃ a b, stepKeep τ i = some a ∧ step τ i = some b ∧ Sim a b := by
  rw [stepKeep_run]
  have same : ∀ {o : Option T}, (stepKeepFn i).run τ = o → step τ i = o →
      ((stepKeepFn i).run τ = none ∧ step τ i = none) ∨
        ∃ a b, (stepKeepFn i).run τ = some a ∧ step τ i = some b ∧ Sim a b := by
    intro o h₁ h₂
    rw [h₁, h₂]
    cases o with
    | none => exact .inl ⟨rfl, rfl⟩
    | some t => exact .inr ⟨t, t, rfl, rfl, Sim.refl t⟩
  have st : ∀ m w, (storeKeep τ m w false [] = none ∧ storeStepK τ m w false [] = none) ∨
      ∃ a b, storeKeep τ m w false [] = some a ∧ storeStepK τ m w false [] = some b ∧ Sim a b := by
    intro m w
    rw [storeKeep_eq, storeStepK_eq]
    exact storeStepKD_spec τ m w false []
  cases i with
  | movdquLoad _ m | movqLoad _ m =>
    refine same (o := bif pub τ m.base then some τ else none) rfl ?_
    show (if memPub τ m = true then some τ else none) = bif pub τ m.base then some τ else none
    cases h : pub τ m.base
    · simp only [memPub, h, Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
    · simp only [memPub, h, ↓reduceIte, Bool.cond_true]
  | movdquStore m _ => exact st m 16
  | movqStore m _ | mmxStore m _ => exact st m 8
  | xop _ | pmuludq _ _ | movdquTbl _ _ _ _ | movqTbl _ _ _ _ => exact same (o := some τ) rfl rfl
  | mop op =>
    refine same (o := bif mopOk τ op then some τ else none) rfl ?_
    simp only [step, Bool.cond_eq_ite]
  | _ =>
    simp only [stepKeepFn, step]
    rw [Taint.stepKeepFn_run, Taint.stepK_eq]
    exact Taint.stepKD_spec τ _

theorem stepKeep_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (hs : stepKeep τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  rcases stepKeep_spec τ i with ⟨h, -⟩ | ⟨a, b, h₁, h₂, hab⟩
  · rw [h] at hs; cases hs
  · rw [h₁] at hs; cases hs
    obtain ⟨h₃, h₄⟩ := step_sound ha h₂ e₁ e₂
    exact ⟨h₃, hab.agree h₄⟩

end VG.X86.SseTaint

namespace VG.X86

/-- Checked scalar and SIMD analysis, sharing the scalar domain and all call rules. -/
def sseTaint : VG.Taint isa := { taint with
  step := SseTaint.stepKeep
  step_sound := SseTaint.stepKeep_sound }

end VG.X86
