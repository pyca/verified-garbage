module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Fn
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.RecoverVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.SignPrecomputed
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub

/-!
# RSASSA-PKCS1-v1_5 on RISC-V, as emitted

`vg_rsa_pkcs1_verify_precomputed`, `vg_rsa_pkcs1_recover_precomputed` and
`vg_rsa_pkcs1_sign_precomputed` with their cleanup
(`Impl.RsaPkcs1Sig.RISCV64.Fn`): each meets its contract in constant time and
returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbed`), which is what its registration binds. What
the cleanup needs of each function's code (`Scrub.scrubSide`) is evaluated
here, by the kernel.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub

theorem verifyPrecomputed :
    VerifiedScrubbed target Impl.RsaPkcs1Sig.RISCV64.Fn.verifyPrecomputed
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi 2128) 32 :=
  verifiedScrubbed (api := Spec.RsaPkcs1Sig.verifyPrecomputedApi) (W := 2128)
    { code := Impl.RsaPkcs1Sig.RISCV64.Precomputed.code, verified := Ver.code_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1VerifyOut _) (by lit_decide)

theorem recoverPrecomputed :
    VerifiedScrubbed target Impl.RsaPkcs1Sig.RISCV64.Fn.recoverPrecomputed
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi 2128) 32 :=
  verifiedScrubbed (api := Spec.RsaPkcs1Sig.recoverPrecomputedApi) (W := 2128)
    { code := Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed.code, verified := Rec.code_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1RecoverOut _) (by lit_decide)

theorem signPrecomputed :
    VerifiedScrubbed target Impl.RsaPkcs1Sig.RISCV64.Fn.signPrecomputed
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi 4432) 32 :=
  verifiedScrubbed (api := Spec.RsaPkcs1Sig.signPrecomputedApi) (W := 4432)
    { code := Impl.RsaPkcs1Sig.RISCV64.Sign.codeP, verified := Sign.codeP_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1SignOut _) (by lit_decide)

end VG.Proof.RsaPkcs1Sig.RISCV64.Fn
