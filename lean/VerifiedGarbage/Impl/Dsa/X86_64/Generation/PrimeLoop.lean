module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.DrawCopy
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SampleRound

/-! # DSA's blinded primality loop with exact whole-draw exhaustion -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

def primeLoopInit : List Instr :=
  [.mov32 .rax (.imm 1), .store (hdr kI) .rax, .mov32 .rax (.imm 0), .store (hdr kUni) .rax]

def tapeCheck : List Instr :=
  [.mov .rcx (.mem (hdr kRandLen)), .mov .rax (.mem (hdr kUsed)), .alu .sub .rcx (.reg .rax),
   .mov .rax (.mem (hdr kLen)), .alu .cmp .rcx (.reg .rax)]

def primeIteration (body : Prog isa) : Prog isa := seqs [
  .block tapeCheck,
  .ite .b (.block [.mov32 .rax (.imm 0), .store (hdr kStat) .rax]) body,
  .block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)]]

def drawRound (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq drawCopy (sampleRound mul round)

def millerRabin (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq (.block primeLoopInit) (.loop (primeIteration (drawRound mul round)) .e)

end VG.Impl.Dsa.X86_64.Generation
