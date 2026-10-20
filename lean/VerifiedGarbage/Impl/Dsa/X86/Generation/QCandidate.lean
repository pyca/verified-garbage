module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Hash
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Shape

/-! # Hash a seed directly into the subgroup candidate and set its endpoint bits -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Pbkdf2.Stream.X86

def qCandidate (H : Hash) (len : Nat) : Prog isa :=
  .seq (seedHash H len) (shape len)
end VG.Impl.Dsa.X86.Generation
