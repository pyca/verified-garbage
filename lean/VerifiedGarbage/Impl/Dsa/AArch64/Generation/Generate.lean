module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output

/-! Complete parameter generation within the persistent search frame. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def generate (G1 G256 : Hash) (mul : Nat → Nat → Nat → Prog isa)
    (roundCode : List (Prog isa)) (pLen qLen : Nat) : Prog isa :=
  .seq (parameterSearch G1 G256 mul roundCode pLen qLen) finishOutput

end VG.Impl.Dsa.AArch64.Generation
