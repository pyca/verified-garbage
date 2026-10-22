module

public import VerifiedGarbage.Impl.Mont.X86.PowerHigh

/-! Public moduli share a short high-bit seed and a padded-modulus fallback. -/

@[expose] public section
namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont

def publicPower (M : Mod) (acc out : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc (M.mo+4*(2*M.n-1)))), .shift .shr .eax 31,
    .alu .cmp .eax (.imm 1)])
    (.ite .e (highPower M acc out (M.n+1)) (powerTwo M acc out (65*M.n)))

end VG.Impl.Mont.X86.Dynamic
