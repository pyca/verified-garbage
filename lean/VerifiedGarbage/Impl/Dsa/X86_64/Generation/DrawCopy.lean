module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Layout
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessCut

/-! # Copy the significant bytes of a whole-limb witness draw

The caller checks tape availability first. The draw's octets (`kLen`) and
the candidate's (`kUsedP`) come from the header: for q160, 24 and 20, so
skip four high bytes, consume all 24, and copy the low 20.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

def drawCopyArgs : List Instr :=
  [.mov .r15 (.reg .rdi), .mov .rsi (.mem (hdr kRand)), .mov .rax (.mem (hdr kUsed)),
   .alu .add .rax (.mem (hdr kLen)), .store (hdr kUsed) .rax, .alu .add .rsi (.reg .rax),
   .mov .rcx (.mem (hdr kUsedP)), .alu .sub .rsi (.reg .rcx),
   .mov .rdi (.mem (hdr kOut)), .mov .rdx (.reg .rcx), .shift .shl .rdx 3]

def drawCopy : Prog isa := seqs [
  .block drawCopyArgs, Ffdh.X86_64.ParameterCandidate.witnessCut,
  .block [.mov .rdi (.reg .r15)]]

end VG.Impl.Dsa.X86_64.Generation
