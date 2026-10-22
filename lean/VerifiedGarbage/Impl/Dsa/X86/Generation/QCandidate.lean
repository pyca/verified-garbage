module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Hash
public import VerifiedGarbage.Impl.Dsa.X86.Generation.QShape

/-! Hash the seed and shape its digest using the existing byte-copy routine. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

def qArguments (digestOffset candidateOffset len : Nat) : List Instr :=
  [.mov .esi (.reg .ebp), .alu .add .esi (.imm (BitVec.ofNat 32 digestOffset)),
   .mov .ebx (.reg .ebp), .alu .add .ebx (.imm (BitVec.ofNat 32 candidateOffset)),
   .mov .ecx (.imm (BitVec.ofNat 32 len))]

def qCandidate (H : Hash) (digestOffset candidateOffset : Nat) : Prog isa :=
  .seq (seedHash H digestOffset)
    (.seq (.block (qArguments digestOffset candidateOffset H.D)) qShape)

end VG.Impl.Dsa.X86.Generation
