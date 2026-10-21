module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-! A local analysis for the fused scan forgets secret UMAAL results and retains its public pointers. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosTaint
open VG VG.Arm

/-- The fused scan's accumulator, source pointers, and public word count. -/
def publicRegs : List Reg := [.r0, .r12, .r4, .lr]

/-- Only this scan's unchanged public registers are retained across a long multiply. -/
def step (τ : VG.Arm.Taint.T) (i : Instr) : Option VG.Arm.Taint.T :=
  match i with
  | .umaal lo hi _ _ =>
    if lo ∉ publicRegs ∧ hi ∉ publicRegs ∧ (RegSet.ofList publicRegs).subset τ.regs = true then
      some (VG.Arm.Taint.ofRegs publicRegs)
    else none
  | _ => taint.step τ i

private theorem umaal_keep {s t : State} {lo hi n m r : Reg}
    (hlo : r ≠ lo) (hhi : r ≠ hi) (h : exec (.umaal lo hi n m) s = some t) :
    t.gpr r = s.gpr r := by
  by_cases same : lo = hi
  · simp only [exec, same, ite_true, reduceCtorEq] at h
  · simp only [exec, same, ite_false, Option.some.injEq] at h
    subst t
    rw [RegUpd.gpr_setReg_of_ne _ _ hhi, RegUpd.gpr_setReg_of_ne _ _ hlo]

private theorem base_step_sound {τ τ' : VG.Arm.Taint.T} {i : Instr}
    {s₁ s₂ s₁' s₂' : State} (ha : VG.Arm.Taint.Agree τ s₁ s₂)
    (hs : VG.Arm.Taint.stepKM τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' :=
  taint.step_sound ha hs e₁ e₂

private theorem umaal_step_sound {τ τ' : VG.Arm.Taint.T} {lo hi n m : Reg}
    {s₁ s₂ s₁' s₂' : State} (ha : VG.Arm.Taint.Agree τ s₁ s₂)
    (hs : step τ (.umaal lo hi n m) = some τ')
    (e₁ : exec (.umaal lo hi n m) s₁ = some s₁')
    (e₂ : exec (.umaal lo hi n m) s₂ = some s₂') :
    addrs (.umaal lo hi n m) s₁ = addrs (.umaal lo hi n m) s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' := by
  change (if lo ∉ publicRegs ∧ hi ∉ publicRegs ∧ (RegSet.ofList publicRegs).subset τ.regs = true then
    some (VG.Arm.Taint.ofRegs publicRegs) else none) = some τ' at hs
  split at hs
  · rename_i keep
    simp only [Option.some.injEq] at hs
    subst τ'
    refine ⟨rfl, VG.Arm.Taint.agree_ofRegs ?_⟩
    intro r hr
    have hlo : r ≠ lo := by intro eq; subst r; exact keep.1 hr
    have hhi : r ≠ hi := by intro eq; subst r; exact keep.2.1 hr
    have old := ha.rf.1 r (RegSet.mem_of_subset keep.2.2 (RegSet.mem_ofList.mpr hr))
    rw [umaal_keep hlo hhi e₁, umaal_keep hlo hhi e₂]
    exact old
  · cases hs

theorem sound {τ τ' : VG.Arm.Taint.T} {i : Instr}
    {s₁ s₂ s₁' s₂' : State} (ha : VG.Arm.Taint.Agree τ s₁ s₂)
    (hs : step τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' := by
  cases i with
  | mov | mvn | dp | adds | adc | subs | cmp | movw | movt | adrSym | rev | mul | mla | ldr | str | ldrb | strb | ldrSp | addSp | alloc | free | push | pop =>
    exact base_step_sound ha hs e₁ e₂
  | umaal => exact umaal_step_sound ha hs e₁ e₂

/-- This untrusted analysis changes no ISA semantics and is proved against the original execution model. -/
def analysis : VG.Taint isa := { taint with step := step, step_sound := sound }

/-- The initial relation is the original ARM register agreement, with no extra assumptions. -/
theorem initialAgree {s t : State} (h : ∀ r ∈ publicRegs, s.gpr r = t.gpr r) :
    VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs publicRegs) s t :=
  VG.Arm.Taint.agree_ofRegs h

end VG.Proof.Bignum.Arm.FiosTaint
