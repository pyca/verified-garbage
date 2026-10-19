module

import VerifiedGarbage.Proof.Dsa.X86.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.X86.Verified
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86.RandomCall
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # The randomized signer, calling the registered `vg_dsa_sign` (x86) -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

/-- The supplied-nonce signer, as registered. -/
def signFn : SignFn where
  name := Spec.Dsa.signApi.name
  code := Entry.operation true
  verified := signing_verified
  noSp := NoSp.of_all (by decide +kernel)
  depth := by decide +kernel

theorem randomSigning_verified :
    Verified target (RandomSign.code signFn.name signFn.code) (Spec.Dsa.randomSignContract abi 156) :=
  randomSign_verified signFn

end VG.Proof.Dsa.X86
