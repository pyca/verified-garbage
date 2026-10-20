module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Impl.Dsa.X86.Generation.QCandidate

/-! # Build q directly in the persistent parameter buffer -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Pbkdf2.Stream.X86

def qBuild (H : Hash) (len : Nat) : Prog isa := .seq (.block qHashArgs) (qCandidate H len)
end VG.Impl.Dsa.X86.Generation
