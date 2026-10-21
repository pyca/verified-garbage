module

public import VerifiedGarbage.Impl.Dsa.X86.Comb
public import VerifiedGarbage.Impl.Dsa.X86.Core

/-! The retained comb uses the ordinary DSA byte input and output routines. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout

def power (prepare : Bool) (len expLen : Nat) (modulus : Field) (a x : Pointer) (output : Nat) : Prog isa :=
  let n := (len+7)/8
  .seq (Core.loadPower n len expLen modulus a x)
    (.seq (call prepare n ((expLen+3)/4)) (Core.store len output))

end VG.Impl.Dsa.X86.Comb
