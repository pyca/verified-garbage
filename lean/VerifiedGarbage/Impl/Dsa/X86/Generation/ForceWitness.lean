module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.QShape
public import VerifiedGarbage.Impl.Dsa.Generation.Layout

/-! Reuse byte shaping for the forced branch of the shared witness sampler. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def clearByte (r : Reg) (mask : BitVec 8) : List Instr :=
  [.movzx8 .eax (at_ r 0), .alu .and .eax (.imm (mask.setWidth 32)), .store8 (at_ r 0) .al]

/-- Edi points to a truncated big-endian draw; clear its top bit and set bit one. -/
def forceWitness (len : Nat) : Prog isa :=
  .seq (.block (clearByte .edi 127))
    (.block ([.mov .ebx (.reg .edi), .alu .add .ebx (.imm (BitVec.ofNat 32 (len - 1)))] ++ forceByte .ebx 2))

def forceStoredWitness (len : Nat) : Prog isa :=
  .seq (.block [.alu .add .edi (.imm (BitVec.ofNat 32 Dsa.Generation.Layout.witness))])
    (.seq (forceWitness len)
      (.block [.alu .sub .edi (.imm (BitVec.ofNat 32 Dsa.Generation.Layout.witness))]))

end VG.Impl.Dsa.X86.Generation
