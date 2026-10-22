module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Montgomery

/-! Fast Montgomery setup, including the padded 160-bit subgroup candidate. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.Mont.X86.Dynamic

/-- Start at the candidate's highest bit, then reach `2^n R` by doubling.
Six Montgomery squares turn this into `R²`, where `R = 2^(64n)`. -/
def montgomerySeed (n bits : Nat) : Prog isa :=
  .seq (setConstW (2 * n) (slot n 4) (2 ^ (bits - 1)))
    (.seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (65 * n - (bits - 1))))])
      (doubleLoop (contextMod n) (slot n 2) (slot n 4)))

def montgomerySquares (n : Nat) : Nat → Prog isa
  | 0 => .block []
  | count + 1 => .seq (montgomery n 4 4 4) (montgomerySquares n count)

def montgomerySetup (n bits : Nat) : Prog isa :=
  .seq (contextStart n) (.seq (montgomerySeed n bits) (montgomerySquares n 6))

end VG.Impl.Dsa.X86.Generation
