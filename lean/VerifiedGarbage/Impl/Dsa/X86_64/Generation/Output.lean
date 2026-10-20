module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch

/-! # Export accepted parameters, or zero the caller's output on every failure -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def outputArgs : List Instr :=
  [.mov .rsi (.mem (sp 40)), .alu .add .rsi (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.packed)),
   .mov .rdi (.mem (sp 48)), .mov .rcx (.mem (sp 56)), .mov .rdx (.reg .rcx), .shift .shl .rdx 3]

def outputCopy : Prog isa :=
  .seq (.block outputArgs)
    (.seq Impl.Ffdh.X86_64.ParameterCandidate.witnessCut (.block [.mov32 .rax (.imm 1)]))

def zeroArgs : List Instr :=
  [.mov .rax (.mem (sp 48)), .store (sp 168) .rax,
   .mov .rax (.mem (sp 56)), .store (sp 184) .rax]

def outputZero : Prog isa :=
  .seq (.block zeroArgs) Impl.RsaOaep.X86_64.zeroOut

def finishOutput : Prog isa :=
  .seq (.block successStatus) (.ite .e outputCopy outputZero)

end VG.Impl.Dsa.X86_64.Generation
