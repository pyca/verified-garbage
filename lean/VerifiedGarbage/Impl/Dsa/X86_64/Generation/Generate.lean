module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output

/-! # Complete parameter generation within the persistent search frame -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Pbkdf2.Md.X86_64

def generate (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (round : Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (parameterSearch G1 G256 sq mul round pLen qLen) finishOutput

end VG.Impl.Dsa.X86_64.Generation
