module

public import VerifiedGarbage.Impl.Bignum.X86_64.R2Words

/-! # A full input word in normalized long division

As `R2Words.step`, with a low dividend word in the second word of the
reciprocal window. The bases of the remainder, modulus, temporary and
window are in `rbx`, `r10`, `r8` and `rbp`; `r12` is the modulus width.
The quotient estimate reads the top two words of the remainder, and the
subtraction includes the low input word. Two masked add-backs finish the
reduction. All branches and addresses depend only on pointers and widths.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.WordReduce

open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- The low word of `r 2^64 + digit - q̂ m`, its product carry and borrow. -/
def subHead : List Instr :=
  [.mov .rax (.mem (at0 .r10)), .mul .rcx, .mov .r9 (.reg .rdx),
    .mov .rdx (.mem { base := .rbp, disp := 8 }), .alu .sub .rdx (.reg .rax),
    .store (at0 .r8) .rdx, cfToRbp]

def mulSub : Prog isa :=
  .seq (.block subHead) (.seq (wordLoop 1 R2Words.subBody) (.block R2Words.subTop))

def step : Prog isa :=
  seqs [.block R2Words.quot, mulSub, R2Words.addBack, R2Words.addBack, R2Words.copyBack]

end VG.Impl.Rsa.X86_64.WordReduce
