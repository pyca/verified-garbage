module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-! `FiosTaint`'s analysis for any list of public registers: a UMAAL whose
outputs are not public forgets everything but them. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2.Taint
open VG VG.Arm

def step (pub : List Reg) (τ : VG.Arm.Taint.T) (i : Instr) : Option VG.Arm.Taint.T :=
  match i with
  | .umaal lo hi _ _ =>
    if lo ∉ pub ∧ hi ∉ pub ∧ (RegSet.ofList pub).subset τ.regs = true then
      some (VG.Arm.Taint.ofRegs pub)
    else none
  | _ => taint.step τ i

private theorem umaal_keep {s t : State} {lo hi n m r : Reg}
    (hlo : r ≠ lo) (hhi : r ≠ hi) (h : exec (.umaal lo hi n m) s = some t) :
    t.gpr r = s.gpr r := by
  by_cases same : lo = hi
  · simp only [reduceExec, same, ite_true, reduceCtorEq] at h
  · simp only [reduceExec, same, ite_false, Option.some.injEq] at h
    subst t
    rw [RegUpd.gpr_setReg_of_ne _ _ hhi, RegUpd.gpr_setReg_of_ne _ _ hlo]

theorem sound (pub : List Reg) {τ τ' : VG.Arm.Taint.T} {i : Instr}
    {s₁ s₂ s₁' s₂' : State} (ha : VG.Arm.Taint.Agree τ s₁ s₂)
    (hs : step pub τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' := by
  cases i with
  | mov | mvn | dp | adds | adc | subs | cmp | movw | movt | adrSym | rev | mul | mla | ldr | str | ldrb
    | strb | ldrSp | addSp | alloc | free | push | pop =>
    exact taint.step_sound ha hs e₁ e₂
  | umaal lo hi n m =>
    change (if lo ∉ pub ∧ hi ∉ pub ∧ (RegSet.ofList pub).subset τ.regs = true then
      some (VG.Arm.Taint.ofRegs pub) else none) = some τ' at hs
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

/-- An untrusted analysis, proved against the execution model. -/
def analysis (pub : List Reg) : VG.Taint isa := { taint with step := step pub, step_sound := sound pub }

end VG.Proof.Bignum.Arm.Fios2.Taint
