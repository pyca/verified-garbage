module

public import VerifiedGarbage.Impl.Mont.X86.ContextSquares
public import VerifiedGarbage.Impl.Mont.X86.PowerHigh

/-! Public-modulus setup for DSA's comb; ordinary secret-modulus power is unchanged. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- For a full-width modulus its high bit supplies a reduced initial power.
After n+1 doublings it reaches 2^(65*n), the same seed as the padded fallback.
The branch observes only the modulus exposed by the comb contract. -/
def seed (n : Nat) : Prog isa :=
  .seq (contextStart n) <|
  .seq (.block [.mov .eax (.mem (sc (slot n 0 + 4*(2*n-1)))), .shift .shr .eax 31,
      .alu .cmp .eax (.imm 1)])
    (.ite .e
      (highPower (contextMod n) (slot n 2) (slot n 4) (n+1))
      (powerTwo (contextMod n) (slot n 2) (slot n 4) (65*n)))

def setup (n : Nat) : Prog isa := .seq (seed n) (setupSquares n)

end VG.Impl.Dsa.X86.Comb
