module

public import VerifiedGarbage.Impl.Bignum.X86_64

/-! # Reject undersized p candidates before consuming witnesses -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- The p byte buffer is in header word 20; CF means p has fewer than L bits. -/
def candidateWidth : List Instr :=
  [.mov .rsi (.mem (hdr 20)), .movzx8 .rax (at0 .rsi), .alu .cmp .rax (.imm 128)]

end VG.Impl.Dsa.X86_64.Generation
