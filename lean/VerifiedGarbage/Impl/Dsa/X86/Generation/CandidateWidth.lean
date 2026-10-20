module
public import VerifiedGarbage.Impl.Mont.X86

/-! # Reject undersized p candidates before drawing any witnesses -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def candidateWidth : List Instr := [.movzx8 .eax (at_ .esi 0), .alu .cmp .eax (.imm 128)]
end VG.Impl.Dsa.X86.Generation
