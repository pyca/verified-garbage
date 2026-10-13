module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReadyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReadyCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant time of the complete verifying entry point -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem VerifyingShaped.branch {reference : VerifyingCall} {s : State} (h : VerifyingShaped reference s) :
    isa.eval (.zero .x .x3) s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  rw [eval_zero, hs.branch, ha.accepted]
  cases reference.input.accepted <;> rfl

theorem VerifyingShaped.x0 {reference : VerifyingCall} {s : State} (h : VerifyingShaped reference s) :
    s.gpr .x0 = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.x0.trans (congrArg ExecutionLayout.base ha.layout)

theorem verifyFailure_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .x0 = B))
    (.block [movi .x0 0])
    (fun _ _ => True) :=
  two_taint [.x0] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

theorem verifyingMain_ct (M : Mont) : RelCT isa (Two VerifyingStart) (SignVerify.verify M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq verifyingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, _⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : VerifyingCall => c.layout.base) (fun _ _ h => h.x0) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (verifyingSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change isa.eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64
