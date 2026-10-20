module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerDetect
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyPowerDetect
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! Generator detection uses no operand-dependent branch or address. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (Operand)

theorem detectTwo_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.detectTwo (fun _ _ => True) := by
  have ready (s : State) (h : ArithmeticReady base len w s) :
      WP isa (VG.Impl.Bignum.Arm.smallConst 5 2) s (ArithmeticReady base len w) :=
    WP.mono (smallConst_ok s 2 h (o := 5) (by decide) (by decide) (by decide) (by decide)) fun _ k => k.1
  unfold VG.Impl.Ffdh.Arm.detectTwo
  exact relCT_chain (smallConst_ct 2 (o := 5) (by decide) (by decide) (by decide)) ready ready
    (equal_ct
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 1)
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 5))

end VG.Proof.Ffdh.Arm
