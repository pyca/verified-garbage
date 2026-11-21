module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Fn
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.DecPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.RndVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub

/-!
# RSAES-PKCS1-v1_5 on RISC-V, as emitted

`vg_rsa_pkcs1_decrypt_precomputed` and `vg_rsa_pkcs1_encrypt_random` with
their cleanup (`Impl.RsaPkcs1Enc.RISCV64.Fn`): each meets its contract in
constant time and returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbedAll`), which is what its registration binds. What
the cleanup needs of each function's code (`Scrub.scrubSide`) is evaluated
here, by the kernel.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub

theorem decryptPrecomputed :
    VerifiedScrubbed target Impl.RsaPkcs1Enc.RISCV64.Fn.decryptPrecomputed
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3456) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPkcs1Enc.decryptPrecomputedApi) (W := 3456)
    { code := Impl.RsaPkcs1Enc.RISCV64.Decrypt.codeP, verified := Dec.codeP_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1DecryptOut _) (by lit_decide)

theorem encryptRandom :
    VerifiedScrubbed target Impl.RsaPkcs1Enc.RISCV64.Fn.encryptRandom
      (Spec.RsaPkcs1Enc.encryptRandomContract abi 4304) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPkcs1Enc.encryptRandomApi) (W := 4304)
    { code := Impl.RsaPkcs1Enc.RISCV64.Random.code, verified := Rnd.code_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1EncryptRandomOut _) (by lit_decide)

end VG.Proof.RsaPkcs1Enc.RISCV64.Fn
