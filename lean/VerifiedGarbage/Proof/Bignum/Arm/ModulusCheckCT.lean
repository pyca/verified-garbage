module
public import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck

import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The modulus validity check has no data-dependent addresses or branches -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem modulusCheck_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r6 = t.gpr .r6) (.block modulusCheck) := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r4, .r6]) ?_ (by taint_decide)
  intro s t _ _ h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

end VG.Proof.Bignum.Arm
