module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape

/-! # FFDH parameter candidates on x86-64: cut random witness bytes to the bound's width -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- Retain all bits through the highest allowed bit, without setting it. -/
def cutMasks : List Instr := shapeMasks ++ [.alu .or .r8 (.reg .r9), .mov32 .r9 (.imm 0)]

/-- `(out = rdi, rand = rsi, len = rcx, bits = rdx)`: copy random bytes
with the excess high bits cleared. The low bit is not changed. -/
def witnessCut : Prog isa := seqs [
  .block cutMasks, .block firstByte, .loop (.block copyByte) .ne]

end VG.Impl.Ffdh.X86_64.ParameterCandidate
