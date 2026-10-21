module

public import VerifiedGarbage.Impl.Bignum.Arm.FusedReduction
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.FusedReduction
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Fused cancellation and quotient formation reveal only public pointers and count. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FusedReduction
open VG VG.Arm

private theorem keeping_r0 {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ s t, P s t → ∀ r ∈ rs, s.gpr r=t.gpr r)
    {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (hc : ((taint.check (Taint.ofRegs rs) c hint).map
      fun τ => (RegSet.ofList [.r0]).subset τ.regs) = some true) :
    RelCT isa P c (fun s t => s.gpr .r0=t.gpr .r0) := by
  intro s t tr₁ tr₂ u v h ex ey
  obtain ⟨τ, ht, ho⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨trace, final⟩ := VG.Taint.check_sound ht (Taint.agree_ofRegs (hp s t h)) ex ey
  exact ⟨trace, final.rf.1 .r0 (RegSet.mem_of_subset ho (RegSet.mem_ofList.mpr (by simp)))⟩

theorem code_relCT : RelCT isa
    (fun s t => s.gpr .r0=t.gpr .r0 ∧ s.gpr .r12=t.gpr .r12 ∧ s.gpr .lr=t.gpr .lr)
    VG.Impl.Bignum.Arm.FusedReduction.code (fun s t => s.gpr .r0=t.gpr .r0) := by
  apply keeping_r0 [.r0,.r12,.lr] ?_ (by taint_decide)
  intro s t h r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem code_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0=t.gpr .r0 ∧ s.gpr .r12=t.gpr .r12 ∧ s.gpr .lr=t.gpr .lr)
    VG.Impl.Bignum.Arm.FusedReduction.code := by
  intro s t tr₁ tr₂ u v _ _ h ex ey
  exact (code_relCT s t tr₁ tr₂ u v h ex ey).1

end VG.Proof.Bignum.Arm.FusedReduction
