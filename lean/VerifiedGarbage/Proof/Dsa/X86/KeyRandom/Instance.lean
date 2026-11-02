module
public import VerifiedGarbage.Proof.Dsa.X86.CheckingVerified
public import VerifiedGarbage.Proof.Dsa.X86.DerivingVerified
public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Call
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Verified

/-! # Key generation calls the registered domain checker and key derivation -/
@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.Impl.Dsa.X86

def checkFn : CheckCall.CheckFn where
  name := "vg_dsa_check_parameters"
  code := Generate.checkParameters
  verified := checking_verified
  noSp := NoSp.of_all (by decide +kernel)
  depth := by decide +kernel

def deriveFn : DeriveFn where
  name := Spec.Dsa.deriveKeyApi.name
  code := Generate.deriveKey
  verified := deriving_verified
  noSp := NoSp.of_all (by decide +kernel)
  depth := by decide +kernel

theorem keyGeneration_verified :
    Verified target (GenerateKey.code checkFn.name deriveFn.name checkFn.code deriveFn.code)
      (Spec.Dsa.generateKeyContract abi 232) := verified checkFn deriveFn
end VG.Proof.Dsa.X86.KeyRandom
