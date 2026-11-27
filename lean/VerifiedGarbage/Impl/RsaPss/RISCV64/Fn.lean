module

public import VerifiedGarbage.Impl.RsaPss.RISCV64.Sign
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# RSASSA-PSS on RISC-V, as emitted

Each function, over the hash functions `f` and `g` of its tables, is its
code, then its cleanup (`Impl.Scrub.RISCV64.scrubAll`): the caller-saved
registers cleared but the 32 bits of its result, and the stack its frames
use, so that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.RsaPss.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)
open VG.Impl.RsaOaep.RISCV64 (Fns)

/-- `vg_rsa_pss_verify_precomputed`. -/
def verifyPrecomputed (f : MdFns) (g : Fns) : Prog isa := scrubAll 32 336 (VG.Impl.RsaPss.RISCV64.verifyPrecomputed f g)

/-- `vg_rsa_pss_sign_precomputed`. -/
def signPrecomputed (f : MdFns) (g : Fns) : Prog isa := scrubAll 32 3488 (Sign.signP f g)

end VG.Impl.RsaPss.RISCV64.Fn
