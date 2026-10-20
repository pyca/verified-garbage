module

public import VerifiedGarbage.Impl.Bignum.Arm.RowCarry
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.RowCarry
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # ARMv7 Montgomery carry propagation: only the top-word pointer is public -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem rowCarry_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0) rowCarry := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0]) ?_ (by taint_decide)
  intro s t _ _ h0
  refine Taint.agree_ofRegs fun r hr => ?_
  have : r = .r0 := by simpa using hr
  subst this
  exact h0

end VG.Proof.Bignum.Arm
