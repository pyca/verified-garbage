module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Decrypt
public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Random
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# RSAES-PKCS1-v1_5 on RISC-V, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.RISCV64.scrub`):
the caller-saved registers cleared but the 32 bits of its result, and the
stack its frames use, so that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_rsa_pkcs1_decrypt_precomputed`. -/
def decryptPrecomputed : Prog isa := scrub 32 3456 Decrypt.codeP

/-- `vg_rsa_pkcs1_encrypt_random`. -/
def encryptRandom : Prog isa := scrub 32 4304 Random.code

end VG.Impl.RsaPkcs1Enc.RISCV64.Fn
