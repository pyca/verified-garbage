module

import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
import VerifiedGarbage.Proof.Rsa.X86_64.CvVerified
import VerifiedGarbage.Proof.Rsa.X86_64.KeyVerified
import VerifiedGarbage.Proof.Rsa.X86_64.Calls
public import VerifiedGarbage.Proof.Rsa.X86_64.InvInstance
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Verified
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKey
public import VerifiedGarbage.Impl.Bignum.X86_64.R2Adx
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Main
import VerifiedGarbage.Proof.Rsa.X86_64.IfmaLit
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSA on x86-64: the proofs `Artifacts/Rsa/X86_64.lean` registers

Each function's `Verified`, made from the proofs of its code and the checks
the kernel evaluates on it (that it inlines, and that every load of MXCSR
restores it).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Instances

open VG.X86_64 VG.Proof.Rsa.X86_64

theorem precompute_verified :
    Verified target (Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.base.mm)
      (Spec.Rsa.publicPrecomputeContract abi 8) :=
  pc_call_verified Proof.Bignum.X86_64.Mont.fnBase (Proof.Bignum.X86_64.R2Impl.words _)
    (by decide +kernel) rfl (by decide +kernel)

theorem precomputeAdx_verified :
    Verified target (Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Bignum.X86_64.R2Adx.choice Proof.Rsa.X86_64.CallMont.adx.mm))
      (Spec.Rsa.publicPrecomputeContract abi 8) :=
  pc_call_verified Proof.Bignum.X86_64.Mont.fnAdx (Proof.Bignum.X86_64.R2Impl.adx _)
    (by decide +kernel) rfl (by decide +kernel)

theorem crtValues_verified :
    Verified target (Impl.Rsa.X86_64.Keys.CrtValues.code)
      (Spec.Rsa.crtValuesContract abi) :=
  cv_verified (by decide +kernel)

theorem checkKey_verified :
    Verified target (Impl.Rsa.X86_64.CheckKey.code)
      (Spec.Rsa.checkKeyContract abi) :=
  Key.key_verified (by decide +kernel)

/-- `vg_rsa_recover_primes_det`, with the batched inverse's instance. -/
theorem recoverDet_verified :
    Verified target Impl.Rsa.X86_64.Keys.RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi) :=
  Rd.rd_verified (by decide +kernel)

end VG.Proof.Rsa.X86_64.Instances
