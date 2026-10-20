module
public import VerifiedGarbage.Impl.Mont.X86

/-! # Force a public out-of-range witness into the RSA-compatible interval

ESI addresses the big-endian witness buffer. Clear its most significant
bit and set bit one; the arithmetic workspace base in EDI is preserved.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def forceWitness (len : Nat) : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .alu .and .eax (.imm 127), .store8 (at_ .esi 0) .al,
   .movzx8 .eax (at_ .esi (len - 1)), .alu .or .eax (.imm 2), .store8 (at_ .esi (len - 1)) .al]
end VG.Impl.Dsa.X86.Generation
