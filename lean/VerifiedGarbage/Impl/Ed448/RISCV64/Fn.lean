module

public import VerifiedGarbage.Impl.Ed448.RISCV64.Whole
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# Ed448 on RISC-V, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.RISCV64.scrub`):
the caller-saved registers cleared but the bits of its result (none for the
public key and signing, 32 for verification), and the stack its frames use,
so that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Ed448.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_ed448_public_key`. -/
def publicKey : Prog isa := scrub 0 1328 Whole.publicKeyCode

/-- `vg_ed448_sign_cached`. -/
def signCached : Prog isa := scrub 0 1696 Whole.signCachedCode

/-- `vg_ed448_verify`. -/
def verify : Prog isa := scrub 32 1616 Whole.verifyCode

end VG.Impl.Ed448.RISCV64.Fn
