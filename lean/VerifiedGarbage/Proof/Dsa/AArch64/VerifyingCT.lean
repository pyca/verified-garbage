module
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingPublic

import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReadyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingPublic
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReadyCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant time of the complete verifying entry point -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem VerifyingShaped.branch {reference : VerifyingCall} {s : State} (h : VerifyingShaped reference s) :
    eval (.zero .x .x3) s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change some (s.gpr .x3 == (0#64)) = _
  rw [hs.branch, ha.accepted]

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

end VG.Proof.Dsa.AArch64
