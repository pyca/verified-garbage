module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output

/-! # Complete parameter generation within the persistent search frame -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Pbkdf2.Md.X86_64

variable {checkName : String}


def generate (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (prime : Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (parameterSearch (checkName := checkName) G1 G256 sq mul prime pLen qLen) finishOutput

end VG.Impl.Dsa.X86_64.Generation
