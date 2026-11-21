module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# PBKDF2 on RISC-V: the function as emitted

PBKDF2 over the functions `F` of one hash function, then its cleanup
(`Impl.Scrub.RISCV64.scrubAll`): the caller-saved registers cleared (it returns
nothing), and all the stack its frames use zeroed, its own two frames and
the `X` bytes below them that HMAC's `init` and `finalize` and their
callees use.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Whole.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)

/-- `vg_pbkdf2_hmac_<hash>` over the functions `F`, as emitted. -/
def pbkdf2 (F : Fns) : Prog isa := scrubAll 0 (F.itB + F.frB + F.X) F.pbkdf2

end VG.Impl.Pbkdf2.Whole.RISCV64.Fn
