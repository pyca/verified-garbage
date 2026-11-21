module

public import VerifiedGarbage.Impl.Argon2.RISCV64.Derive
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# Argon2 on RISC-V: the function as emitted

`vg_argon2`, then its cleanup (`Impl.Scrub.RISCV64.scrubAll`): the
caller-saved registers cleared (it returns nothing), and the 320 bytes of
stack its frames and those of the functions it calls use zeroed. Its
arguments on the stack are in the caller's frame, among the buffers, which
the caller owns.
-/

@[expose] public section

namespace VG.Impl.Argon2.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)

/-- `vg_argon2`, as emitted. -/
def derive : Prog isa := scrubAll 0 320 Impl.Argon2.RISCV64.Derive.derive

end VG.Impl.Argon2.RISCV64.Fn
