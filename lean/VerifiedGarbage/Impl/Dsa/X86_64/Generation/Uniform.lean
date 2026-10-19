module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Layout

/-! # Record whether the current witness was sampled uniformly -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.RsaKeyGen.X86_64.Candidate

def saveUniform : List Instr :=
  [.mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax), .store (hdr kU) .rcx,
   .alu .test .rax (.reg .rax)]

end VG.Impl.Dsa.X86_64.Generation
