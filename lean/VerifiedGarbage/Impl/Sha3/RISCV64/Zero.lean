module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# SHA-3 on RISC-V: zeroing a state

`zeroState b`: the 25 lanes of the Keccak state at `b` set to zero (the
sponge's state before any input), through `t0`. Callers of the sponge
functions (`Impl/Sha3/RISCV64/Stream.lean`) start a hash with it.
-/

@[expose] public section

namespace VG.Impl.Sha3.RISCV64

open VG.RISCV64

/-- The Keccak state at `[b]` zeroed, through `t0`. -/
def zeroState (b : Reg) : List Instr :=
  [.li .t0 0] ++ (List.range 25).flatMap fun k => [.store .d .t0 b (8 * k)]

end VG.Impl.Sha3.RISCV64
