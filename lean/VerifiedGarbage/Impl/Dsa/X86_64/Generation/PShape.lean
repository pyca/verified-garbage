module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Impl.Mgf1.X86_64

/-! # Shape the suffix of the concatenated p-candidate hashes -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Mgf1.X86_64

def pShapeArgs (len count plen : Nat) : List Instr :=
  [.mov .rsi (.mem (sp 32)),
   .alu .add .rsi (.imm (BitVec.ofNat 32 ((count + 1) * len - plen))),
   .mov .rdi (.mem (sp 0)), .mov32 .rcx (.imm plen),
   .mov32 .rdx (.imm (BitVec.ofNat 32 (8 * plen)))]

def pShape (len count plen : Nat) : Prog isa :=
  .seq (.block (pShapeArgs len count plen)) Ffdh.X86_64.ParameterCandidate.shape

end VG.Impl.Dsa.X86_64.Generation
