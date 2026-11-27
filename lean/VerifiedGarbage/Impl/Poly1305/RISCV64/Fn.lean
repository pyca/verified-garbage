module

public import VerifiedGarbage.Impl.Poly1305.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# Poly1305 on RISC-V: the functions as emitted

`vg_poly1305_init`, `vg_poly1305_update` and `vg_poly1305_finalize`, then
their cleanup (`Impl.Scrub.RISCV64.scrubAll`): the caller-saved registers
cleared (they return nothing). None uses the stack, so none zeroes any.
-/

@[expose] public section

namespace VG.Impl.Poly1305.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)

/-- `vg_poly1305_init`, as emitted. -/
def init : Prog isa := scrubAll 0 0 Impl.Poly1305.RISCV64.init

/-- `vg_poly1305_update`, as emitted. -/
def update : Prog isa := scrubAll 0 0 Impl.Poly1305.RISCV64.update

/-- `vg_poly1305_finalize`, as emitted. -/
def finalize : Prog isa := scrubAll 0 0 Impl.Poly1305.RISCV64.finalize

end VG.Impl.Poly1305.RISCV64.Fn
