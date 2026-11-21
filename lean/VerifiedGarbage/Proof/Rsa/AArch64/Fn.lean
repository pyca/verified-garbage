module

public import VerifiedGarbage.Impl.Rsa.AArch64.Fn
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.CvVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.RdVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.CkVerified
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.AArch64.Scrub

/-!
# RSA's key functions on AArch64, as emitted

`vg_rsa_public_precompute`, `vg_rsa_private_precompute`, `vg_rsa_crt_values`,
`vg_rsa_recover_primes_det` and `vg_rsa_check_key` with their cleanup
(`Impl.Rsa.AArch64.Fn`): each meets its contract in constant time and returns
without secret residue (`VerifiedScrubbed`), which is what its registration
binds. What the cleanup needs of each function's code (`Scrub.scrubSide`)
is evaluated here, by the kernel.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Fn

open VG.AArch64 VG.AArch64.Scrub

theorem publicPrecompute :
    VerifiedScrubbed target Impl.Rsa.AArch64.Fn.publicPrecompute
      (Spec.Rsa.publicPrecomputeContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.publicPrecomputeApi)
    { code := Impl.Rsa.AArch64.Precompute.code Impl.Bignum.AArch64.SquareEightCall.mm,
      verified := Proof.Bignum.AArch64.precompute_verified Proof.Bignum.AArch64.Mont.base } _
    (Scrub.publicPrecomputeOk _) (by dsimp only; lit_decide)

theorem privatePrecompute :
    VerifiedScrubbed target Impl.Rsa.AArch64.Fn.privatePrecompute
      (Spec.Rsa.privatePrecomputeContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.privatePrecomputeApi)
    { code := Impl.Rsa.AArch64.PrivPre.code Impl.Bignum.AArch64.SquareEightCall.mm,
      verified := Proof.Bignum.AArch64.PrivPre.privPre_verified Proof.Bignum.AArch64.Mont.base } _
    (Scrub.privatePrecomputeOk _) (by dsimp only; lit_decide)

theorem crtValues [InvLaw] :
    VerifiedScrubbed target Impl.Rsa.AArch64.Fn.crtValues (Spec.Rsa.crtValuesContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.crtValuesApi)
    { code := Impl.Rsa.AArch64.Keys.CrtValues.code, verified := cv_verified } _
    (Scrub.crtValuesOk _) (by dsimp only; lit_decide)

theorem recoverPrimesDet [GcdLaw VG.Impl.Rsa.AArch64.RecoverDet.gcdB] :
    VerifiedScrubbed target Impl.Rsa.AArch64.Fn.recoverPrimesDet
      (Spec.Rsa.recoverPrimesDetContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.recoverPrimesDetApi)
    { code := Impl.Rsa.AArch64.RecoverDet.code, verified := Rd.rd_verified } _
    (Scrub.recoverPrimesDetOk _) (by dsimp only; lit_decide)

theorem checkKey :
    VerifiedScrubbed target Impl.Rsa.AArch64.Fn.checkKey (Spec.Rsa.checkKeyContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.checkKeyApi)
    { code := Impl.Rsa.AArch64.CheckKey.code, verified := ck_verified } _
    (Scrub.checkKeyOk _) (by dsimp only; lit_decide)

end VG.Proof.Rsa.AArch64.Fn
