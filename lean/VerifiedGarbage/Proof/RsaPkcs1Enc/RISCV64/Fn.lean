module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomPublic
public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Fn
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.DecPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.RndVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub

/-!
# RSAES-PKCS1-v1_5 on RISC-V, as emitted

`vg_rsa_pkcs1_encrypt_random` with its cleanup
(`Impl.RsaPkcs1Enc.RISCV64.Fn`): it meets its contract in constant time and
returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbedAll`), which is what its registration binds
(decryption's is in `Front.lean`). What the cleanup needs of its code
(`Scrub.scrubSide`) is evaluated here, by the kernel.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub

theorem encryptRandom_asked :
    VerifiedScrubbed target Impl.RsaPkcs1Enc.RISCV64.Fn.encryptRandom
      (Proof.RsaPkcs1Enc.encryptRandomAskedContract abi 4304) 32 :=
  verifiedScrubbedAll (api := Proof.RsaPkcs1Enc.encryptRandomAskedApi) (W := 4304)
    { code := Impl.RsaPkcs1Enc.RISCV64.Random.code, verified := Rnd.code_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1EncryptRandomOut _) (by lit_decide)

theorem encryptRandom :
    VerifiedScrubbed target
      Impl.RsaPkcs1Enc.RISCV64.Fn.encryptRandom
      (Spec.RsaPkcs1Enc.encryptRandomContract abi 4304) 32 :=
  encryptRandom_imp (encryptRandom_asked) id

theorem encryptRandom_public :
    Spec.RsaPkcs1Enc.encryptRandomOut.Of abi
      Impl.RsaPkcs1Enc.RISCV64.Fn.encryptRandom
      (Spec.RsaPkcs1Enc.encryptRandomContract abi 4304) :=
  Proof.RsaPkcs1Enc.encryptRandom_public (encryptRandom_asked)

end VG.Proof.RsaPkcs1Enc.RISCV64.Fn
