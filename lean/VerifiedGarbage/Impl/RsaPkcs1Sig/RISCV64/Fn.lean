module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Sign
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# RSASSA-PKCS1-v1_5 on RISC-V, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.RISCV64.scrub`):
the caller-saved registers cleared but the 32 bits of its result, and the
stack its frames use, so that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_rsa_pkcs1_verify_precomputed`. -/
def verifyPrecomputed : Prog isa := scrub 32 2128 Precomputed.code

/-- `vg_rsa_pkcs1_recover_precomputed`. -/
def recoverPrecomputed : Prog isa := scrub 32 2128 RecoverPrecomputed.code

/-- `vg_rsa_pkcs1_sign_precomputed`. -/
def signPrecomputed : Prog isa := scrub 32 4432 Sign.codeP

end VG.Impl.RsaPkcs1Sig.RISCV64.Fn
