module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Vector

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Neon.Pair
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Two states, with corresponding 64-bit words packed together. -/
def load (p : Reg) : List Instr :=
  (List.range 25).map fun i => .ldrq (vreg i) p (16*i)

def store (p : Reg) : List Instr :=
  (List.range 25).map fun i => .strq (vreg i) p (16*i)

/-- Keep each round as a short structured block for kernel evaluation. -/
def roundsProg (sha3 : Bool) : Nat → Prog isa
  | 0 => .block []
  | n+1 => .seq (roundsProg sha3 n) (.block (if sha3 then
      Impl.Sha3.AArch64.Sha3.Vector.round n else Vector.round n))

end VG.Impl.Sha3.AArch64.Neon.Pair
