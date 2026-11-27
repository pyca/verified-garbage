module

public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Impl.Xdh.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# X448 on RISC-V, as emitted

`vg_x448_exchange` (`Impl.Xdh.RISCV64.exchange` calling `vg_x448`) and
`vg_x448_base`, each followed by its cleanup (`Impl.Scrub.RISCV64.scrubAll`):
the stack its frames use zeroed (16 bytes, none), then the caller-saved
registers cleared but the result's bits (32, none).
-/

@[expose] public section

namespace VG.Impl.X448.RISCV64.Fn

open VG.RISCV64 VG.Impl.Scrub.RISCV64

/-- `vg_x448_exchange`: the check of `vg_x448`'s result, then its cleanup. -/
def exchange : Prog isa := scrubAll 32 16 (Impl.Xdh.RISCV64.exchange "vg_x448" Impl.X448.RISCV64.R64.x448 56)

/-- `vg_x448_base`, then its cleanup. -/
def base : Prog isa := scrubAll 0 0 Impl.X448.RISCV64.R64.x448Base

end VG.Impl.X448.RISCV64.Fn
