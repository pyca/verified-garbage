module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessCut
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Mgf1.X86_64

/-! # Pack generated domain values for the existing verified domain check -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def packArgs (src dst len : Nat) : List Instr :=
  [.mov .rsi (.mem (sp 40)), .mov .rdi (.reg .rsi),
   .alu .add .rsi (.imm (BitVec.ofNat 32 src)), .alu .add .rdi (.imm (BitVec.ofNat 32 dst)),
   .mov32 .rcx (.imm (BitVec.ofNat 32 len)), .mov32 .rdx (.imm (BitVec.ofNat 32 (8 * len)))]

def packPart (src dst len : Nat) : Prog isa :=
  .seq (.block (packArgs src dst len)) Impl.Ffdh.X86_64.ParameterCandidate.witnessCut

def pack (pLen qLen : Nat) : Prog isa :=
  seqs [packPart VG.Impl.Dsa.Generation.Layout.p VG.Impl.Dsa.Generation.Layout.packed pLen,
    packPart VG.Impl.Dsa.Generation.Layout.q (VG.Impl.Dsa.Generation.Layout.packed + pLen) qLen,
    packPart VG.Impl.Dsa.Generation.Layout.g (VG.Impl.Dsa.Generation.Layout.packed + pLen + qLen) pLen]

end VG.Impl.Dsa.X86_64.Generation
