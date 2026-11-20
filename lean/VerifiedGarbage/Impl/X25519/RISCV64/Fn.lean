module

public import VerifiedGarbage.Impl.X25519.RISCV64.R64
public import VerifiedGarbage.Impl.X25519.RISCV64.Base
public import VerifiedGarbage.Impl.Xdh.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# X25519 on RISC-V, as emitted

`vg_x25519_exchange` (`Impl.Xdh.RISCV64.exchange` calling `vg_x25519`) and
`vg_x25519_base`, each followed by its cleanup
(`Impl.Scrub.RISCV64.scrub`): the stack its frames use zeroed (16 bytes,
none), then the caller-saved registers cleared but the result's bits (32,
none).
-/

@[expose] public section

namespace VG.Impl.X25519.RISCV64.Fn

open VG.RISCV64 VG.Impl.Scrub.RISCV64

/-- `vg_x25519_exchange`: the check of `vg_x25519`'s result, then its cleanup. -/
def exchange : Prog isa := scrub 32 16 (Impl.Xdh.RISCV64.exchange "vg_x25519" Impl.X25519.RISCV64.R64.x25519 32)

/-- `vg_x25519_base`, then its cleanup. -/
def base : Prog isa := scrub 0 0 Impl.X25519.RISCV64.Base.x25519Base

end VG.Impl.X25519.RISCV64.Fn
