module

public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector

/-! # Two interleaved Keccak states: loading and storing them in the vector registers -/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Neon.Pair

open VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Lane `i` of both states at `r` in `v<i>`. -/
def load (r : Reg) : List Instr := (List.range 25).map fun i => .ldrq (vreg i) r (16 * i)

def store (r : Reg) : List Instr := (List.range 25).map fun i => .strq (vreg i) r (16 * i)

end VG.Impl.Sha3.AArch64.Neon.Pair
