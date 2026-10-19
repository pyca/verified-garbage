module

public import VerifiedGarbage.TCB.X86_64.Isa

/-! # RSA's forced witness branch for DSA candidates

The witness has already been truncated to the candidate's byte width.
Clear its top bit and set bit 1, including when a 160-bit value will be
loaded into a padded four-limb Montgomery workspace.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64

def forceWitness (len : Nat) : List Instr :=
  [.movzx8 .rax { base := .rdi }, .alu .and .rax (.imm 127),
   .store8 { base := .rdi } .rax,
   .movzx8 .rax { base := .rdi, disp := (len - 1 : Nat) }, .alu .or .rax (.imm 2),
   .store8 { base := .rdi, disp := (len - 1 : Nat) } .rax]

end VG.Impl.Dsa.X86_64.Generation
