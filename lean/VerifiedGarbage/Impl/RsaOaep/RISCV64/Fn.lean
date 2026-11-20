module

public import VerifiedGarbage.Impl.RsaOaep.RISCV64.Decrypt
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# RSAES-OAEP on RISC-V, as emitted

Each function, over the hash functions `f` of its tables, is its code, then
its cleanup (`Impl.Scrub.RISCV64.scrub`): the caller-saved registers cleared
but the 32 bits of its result, and the stack its frames use, so that it
returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_rsa_oaep_decrypt_precomputed`. -/
def decryptPrecomputed (f : Fns) : Prog isa := scrub 32 3488 (Dec.decryptP f)

/-- `vg_rsa_oaep_encrypt_precomputed`. -/
def encryptPrecomputed (f : Fns) : Prog isa := scrub 32 336 (encrypt f)

end VG.Impl.RsaOaep.RISCV64.Fn
