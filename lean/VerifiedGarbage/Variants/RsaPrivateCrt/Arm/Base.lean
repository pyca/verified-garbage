module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified

/-! # ARMv7 private CRT and its associated public operations -/

@[expose] public section
namespace VG.Variants.RsaPrivateCrt.Arm.Base
open VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : Proof.Rsa.Arm.CrtImpl where
  name := Spec.Rsa.privateCrtApi.name
  code := CrtFn.code
  verified := crt_verified
  stack := by decide +kernel
  pcName := Spec.Rsa.publicPrecomputeApi.name
  pc := PcFn.code
  pcVerified := precompute_verified
  pcStack := by decide +kernel
  pdName := Spec.Rsa.publicPrecomputedCheckedApi.name
  pd := PdFn.code
  pdVerified := pd_verified
  pdStack := by decide +kernel
  suffix := ""
  features := []
end VG.Variants.RsaPrivateCrt.Arm.Base
