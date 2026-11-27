module

public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallContract
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallCT
import VerifiedGarbage.Proof.Framework.Lit

/-! # The baseline callable Montgomery product and square -/

@[expose] public section
namespace VG.Proof.Variants.RsaMont.Arm.Base
open VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : MontBackend where
  mul := MontCall.code
  verified := montCall_verified
  correct := montCallFn_ok
  rawCT := montCallFn_ct
  stackOk := by decide +kernel
  mulOk := by lit_decide
  callerOk := fun _ _ h => h
  suffix := ""
  features := []

end VG.Proof.Variants.RsaMont.Arm.Base
