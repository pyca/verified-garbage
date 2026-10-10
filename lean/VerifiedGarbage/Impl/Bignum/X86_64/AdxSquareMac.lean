import VerifiedGarbage.Impl.Bignum.X86_64.Adx

/-!
# Building blocks for an ADX square

A square needs each off-diagonal product only once. The multiply-add below
keeps the scalar in `rdx`, so it does not overwrite words below the accumulator
window as the integrated Montgomery multiplier does. That distinction matters
when earlier words still hold the unreduced square.
-/

namespace VG.Impl.Bignum.X86_64.AdxSquare

open VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Adx

/-- Add `rdx` times four input words to four accumulator words and `rcx`.
The low words end in `r11`, `r12`, `r13`, `r15`; the carry ends in `rcx`.
Neither memory nor the scalar changes. -/
def mac4 : List Instr :=
  ([.alu32 .xor .rsi (.reg .rsi)] : List Instr) ++ (wordA 0 .rax .r11 .rcx ++
    (wordA 1 .rsi .r12 .rax ++ (wordA 2 .rax .r13 .rsi ++ (wordA 3 .rcx .r15 .rax ++ close .rcx))))

/-- Four multiply-add words stored, advancing the public word counter. -/
def mac4Store : List Instr := mac4 ++
  ([.store (ix .r8 .r14) .r11, .store (ix .r8 .r14 8) .r12, .store (ix .r8 .r14 16) .r13,
    .store (ix .r8 .r14 24) .r15, .alu .add .r14 (.imm 4), .alu .cmp .r14 (.reg .rbx)] : List Instr)

/-- One multiply-add word, for a row's one to three remaining words. -/
def mac1 : List Instr :=
  ([.alu32 .xor .rsi (.reg .rsi), .mov .rax (.reg .rcx)] : List Instr) ++
    (wordA 0 .rcx .r11 .rax ++ close .rcx)

/-- One multiply-add word stored, advancing the public word counter. -/
def mac1Store : List Instr := mac1 ++
  ([.store (ix .r8 .r14) .r11, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .rbx)] : List Instr)

/-- The rounded block limit and initial carry/counter. `rbp` is the public
row length and `rdx` the scalar. -/
def rowStart : List Instr :=
  [.mov .rbx (.reg .rbp), .shift .shr .rbx 2, .alu .add .rbx (.reg .rbx), .alu .add .rbx (.reg .rbx),
    .mov32 .rcx (.imm 0), .mov32 .r14 (.imm 0), .alu .cmp .rbx (.imm 0)]

/-- Restore the exact row length for the remaining words. -/
def rowRemainder : List Instr :=
  [.mov .rbx (.reg .rbp), .alu .cmp .r14 (.reg .rbx)]

/-- Add `rdx` times `rbp` words at `r9` to the words at `r8`, returning the
carry in `rcx`. All loop bounds are public; no header or low accumulator
word is used as a scalar spill slot. -/
def macRow : Prog isa :=
  .seq (.block rowStart)
    (.seq (.ite .ne (.loop (.block mac4Store) .ne) (.block []))
      (.seq (.block rowRemainder)
        (.ite .ne (.loop (.block mac1Store) .ne) (.block []))))

end VG.Impl.Bignum.X86_64.AdxSquare
