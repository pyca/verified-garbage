module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Layout
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessCut

/-! # Copy the significant bytes of a whole-limb witness draw

The caller checks tape availability first. For q160, drawBytes is 24 and
len is 20: skip four high bytes, consume all 24, and copy the low 20.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

def drawCopyArgs (len drawBytes : Nat) : List Instr :=
  [.mov .r15 (.reg .rdi), .mov .rsi (.mem (hdr kRand)), .mov .rax (.mem (hdr kUsed)),
   .alu .add .rsi (.reg .rax), .alu .add .rsi (.imm (BitVec.ofNat 32 (drawBytes - len))),
   .alu .add .rax (.imm (BitVec.ofNat 32 drawBytes)), .store (hdr kUsed) .rax,
   .mov .rdi (.mem (hdr kOut)), .mov32 .rcx (.imm (BitVec.ofNat 32 len)),
   .mov32 .rdx (.imm (BitVec.ofNat 32 (8 * len)))]

def drawCopy (len drawBytes : Nat) : Prog isa := seqs [
  .block (drawCopyArgs len drawBytes), Ffdh.X86_64.ParameterCandidate.witnessCut,
  .block [.mov .rdi (.reg .r15)]]

end VG.Impl.Dsa.X86_64.Generation
