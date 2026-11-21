module

public import VerifiedGarbage.Impl.Rsa.RISCV64.Fn
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreVerified
public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreVerified
public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValVerified
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCkV
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub

/-!
# RSA's key functions on RISC-V, as emitted

`vg_rsa_public_precompute`, `vg_rsa_private_precompute`, `vg_rsa_crt_values`,
`vg_rsa_check_key` and `vg_rsa_recover_primes_det` with their cleanup
(`Impl.Rsa.RISCV64.Fn`): each meets its contract in constant time and returns
without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbedAll`), which is what its registration binds. What
the cleanup needs of each function's code (`Scrub.scrubSide`) is evaluated
here, by the kernel.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub

theorem publicPrecompute :
    VerifiedScrubbed target Impl.Rsa.RISCV64.Fn.publicPrecompute
      (Spec.Rsa.publicPrecomputeContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.publicPrecomputeApi) (W := 0)
    { code := Impl.Bignum.RISCV64.Precompute.precompute,
      verified := Proof.Bignum.RISCV64.Pre.precompute_verified }
    (Scrub.publicPrecomputeOut 0) (by lit_decide)

theorem privatePrecompute :
    VerifiedScrubbed target Impl.Rsa.RISCV64.Fn.privatePrecompute
      (Spec.Rsa.privatePrecomputeContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.privatePrecomputeApi) (W := 0)
    { code := Impl.Bignum.RISCV64.PrivPre.code,
      verified := Proof.Bignum.RISCV64.PrivPre.pp_verified }
    (Scrub.privatePrecomputeOut 0) (by lit_decide)

/-- What the cleanup needs of `vg_rsa_crt_values`'s code, stated without
the inverse's law its proof takes. -/
theorem crtValues_side : scrubSide Impl.Rsa.RISCV64.CrtValues.code 0 32 [] = true := by lit_decide

theorem crtValues [InvLaw] :
    VerifiedScrubbed target Impl.Rsa.RISCV64.Fn.crtValues (Spec.Rsa.crtValuesContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.crtValuesApi) (W := 0)
    { code := Impl.Rsa.RISCV64.CrtValues.code, verified := CrtValues.crtValues_verified }
    (Scrub.crtValuesOut 0) crtValues_side

theorem checkKey :
    VerifiedScrubbed target Impl.Rsa.RISCV64.Fn.checkKey (Spec.Rsa.checkKeyContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.checkKeyApi) (W := 0)
    { code := Impl.Rsa.RISCV64.CheckKey.code, verified := KeyCheck.ck_verified }
    (Scrub.checkKeyOut 0) (by lit_decide)

/-- What the cleanup needs of `vg_rsa_recover_primes_det`'s code, stated
without the inverse's law its proof takes. -/
theorem recoverPrimesDet_side : scrubSide Impl.Rsa.RISCV64.RecoverDet.code 0 32 [] = true := by
  lit_decide

theorem recoverPrimesDet [InvLaw] :
    VerifiedScrubbed target Impl.Rsa.RISCV64.Fn.recoverPrimesDet
      (Spec.Rsa.recoverPrimesDetContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.recoverPrimesDetApi) (W := 0)
    { code := Impl.Rsa.RISCV64.RecoverDet.code, verified := RecDet.rd_verified }
    (Scrub.recoverPrimesDetOut 0) recoverPrimesDet_side

end VG.Proof.Rsa.RISCV64.Fn
