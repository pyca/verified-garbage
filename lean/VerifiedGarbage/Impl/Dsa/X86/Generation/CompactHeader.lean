module

public import VerifiedGarbage.Impl.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Mont

/-! Initialize the shared 64-bit-limb header using native 32-bit stores. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def storeHeaderWord (offset : Nat) : List Instr :=
  [.store (sc offset) .eax, .store (sc (offset + 4)) .edx]

def compactHeaderStart (w : Nat) : List Instr :=
  [.mov .edx (.imm 0), .mov .eax (.imm (BitVec.ofNat 32 w))] ++ storeHeaderWord 48 ++
  [.mov .eax (.imm (BitVec.ofNat 32 (8 * (w + 2))))] ++ storeHeaderWord 224

def compactHeaderPointer (w j : Nat) : List Instr :=
  [.mov .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 (Spec.Rsa.Mont.arrAt w j)))] ++
  storeHeaderWord (64 + 8 * j)

def compactHeader (w : Nat) : List Instr :=
  compactHeaderStart w ++ (List.range 8).flatMap (compactHeaderPointer w)

end VG.Impl.Dsa.X86.Generation
