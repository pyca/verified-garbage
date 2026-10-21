module

public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-! # Every candidate attempt starts with an empty output buffer -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateClear
open VG VG.X86 VG.Impl.Mont.X86

def args : List Instr := [.mov .esi (.mem (sc 0)), .mov .ecx (.mem (sc 4)), .mov .eax (.imm 0)]

def code : Prog isa :=
  .seq (.block args)
    (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne)

end VG.Impl.RsaKeyGen.X86.CandidateClear
