module

public import VerifiedGarbage.Impl.Bignum.Arm.ExpControls
import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.ExpControls
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Exponent control slots are written at fixed offsets from the public workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem expControls_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
    (.block expControls) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h

end VG.Proof.Bignum.Arm
