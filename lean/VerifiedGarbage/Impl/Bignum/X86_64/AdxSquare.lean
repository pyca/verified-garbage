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
  [.alu32 .xor .rsi (.reg .rsi)] ++ (wordA 0 .rax .r11 .rcx ++
    (wordA 1 .rsi .r12 .rax ++ (wordA 2 .rax .r13 .rsi ++ (wordA 3 .rcx .r15 .rax ++ close .rcx))))

/-- Four multiply-add words stored, advancing the public word counter. -/
def mac4Store : List Instr := mac4 ++
  [.store (ix .r8 .r14) .r11, .store (ix .r8 .r14 8) .r12, .store (ix .r8 .r14 16) .r13,
    .store (ix .r8 .r14 24) .r15, .alu .add .r14 (.imm 4), .alu .cmp .r14 (.reg .rbx)]

/-- One multiply-add word, for a row's one to three remaining words. -/
def mac1 : List Instr :=
  [.alu32 .xor .rsi (.reg .rsi), .mov .rax (.reg .rcx)] ++
    (wordA 0 .rcx .r11 .rax ++ close .rcx)

/-- One multiply-add word stored, advancing the public word counter. -/
def mac1Store : List Instr := mac1 ++
  [.store (ix .r8 .r14) .r11, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .rbx)]

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

/-- Store a row's final carry and advance the public row index and window. -/
def crossTail : List Instr :=
  [.store (ix .r8 .r14) .rcx, .alu .add .r8 (.imm 8), .alu .add .rbp (.imm 1),
    .alu .cmp .rbp (.reg .r10)]

/-- Row `i` adds `a_i` times `a_0, …, a_{i-1}` at word `i` of the product.
Only products strictly below the diagonal are accumulated. -/
def crossRow : Prog isa :=
  .seq (.block [.mov .rdx (.mem (ix .r9 .rbp))])
    (.seq macRow (.block crossTail))

/-- Clear the product buffer, then accumulate its off-diagonal products.
`r8` addresses `2 w + 2` words; `r9` addresses the input; `rbx = w ≥ 2`. -/
def cross : Prog isa :=
  .seq Adx.zeroWin (.seq (.block [.mov .r10 (.reg .rbx), .mov32 .rbp (.imm 1), .alu .add .r8 (.imm 8)])
    (.loop crossRow .ne))

/-- Double two cross-product words, add the square of `rdx`, and the carry
in `r15`. The result is `rbx:r12:r11`; the two ADX chains add the diagonal
and double the cross products independently. -/
def diagonalCore : List Instr :=
  [.alu32 .xor .rsi (.reg .rsi), .mov32 .rbx (.imm 0), .mulx .rax .rcx (.reg .rdx),
    .adcx .r11 (.reg .r11), .adox .r11 (.reg .rcx),
    .adcx .r12 (.reg .r12), .adox .r12 (.reg .rax),
    .adcx .rbx (.reg .rsi), .adox .rbx (.reg .rsi),
    .adcx .r11 (.reg .r15), .adcx .r12 (.reg .rsi), .adcx .rbx (.reg .rsi)]

def diagonalHead : List Instr :=
  [.mov .rdx (.mem (ix .r9 .rbp)), .mov .r11 (.mem (ix .r8 .r14)),
    .mov .r12 (.mem (ix .r8 .r14 8))]

def diagonalTail : List Instr :=
  [.store (ix .r8 .r14) .r11, .store (ix .r8 .r14 8) .r12, .mov .r15 (.reg .rbx),
    .alu .add .rbp (.imm 1), .alu .add .r14 (.imm 2), .alu .cmp .rbp (.reg .r10)]

/-- Process one pair of cross-product words and one diagonal product. -/
def diagonalStep : Prog isa :=
  .seq (.block diagonalHead) (.seq (.block diagonalCore) (.block diagonalTail))

/-- Double the cross products and add every diagonal square. `r10 = w > 0`,
`r8` is the product buffer and `r9` the input. -/
def diagonal : Prog isa :=
  .seq (.block [.mov32 .r15 (.imm 0), .mov32 .rbp (.imm 0), .mov32 .r14 (.imm 0)])
    (.loop diagonalStep .ne)

/-- The unreduced square, at `aAcc + 16`, using the adjacent `aAcc` and
`aTmp` storage. Each off-diagonal product is computed only once. -/
def rawSquare (a : Nat) : Prog isa :=
  .seq (.block (Adx.setup a)) (.seq cross
    (.seq (.block (Adx.setup a)) (.seq (.block [.mov .r10 (.reg .rbx)]) diagonal)))

/-- Montgomery cancellation multiplier for the window's low word. -/
def redcHead : List Instr :=
  [.mov .rdx (.mem (at0 .r8)), .mulx .rax .rdx (.mem (hdr sMinv))]

/-- Add the multiplication carry and the previous row's high carry to the
window's top word. The new high carry stays in `r10`, avoiding propagation
through the still-unprocessed upper half of the square. -/
def redcTail : List Instr :=
  [.mov .rax (.mem (ix .r8 .r14)), .mov32 .rsi (.imm 0),
    .alu .add .rax (.reg .rcx), .alu .adc .rsi (.imm 0),
    .alu .add .rax (.reg .r10), .alu .adc .rsi (.imm 0),
    .store (ix .r8 .r14) .rax, .mov .r10 (.reg .rsi), .alu .add .r8 (.imm 8)]

/-- One Montgomery cancellation row. `r9` is the modulus, `rbp` its length,
`r8` the moving window and `r10` the pending high carry. -/
def redcRow : Prog isa :=
  .seq (.block redcHead) (.seq macRow (.seq (.block redcTail) (.block Adx.rowEnd)))

def redcSetup : List Instr :=
  [.mov .r8 (.mem (hdr (sArr Public.aAcc))), .alu .add .r8 (.imm 16),
    .mov .r9 (.mem (hdr (sArr Public.aN))), .mov .rbp (.mem (hdr sW)), .mov32 .r10 (.imm 0)]

/-- Materialize the last row's high carry in the result's padding words. -/
def redcFinish : List Instr :=
  [.store (ix .r8 .rbp) .r10, .mov32 .rax (.imm 0), .store (ix .r8 .rbp 8) .rax]

/-- Montgomery reduction of the `2 w` words at `aAcc + 16`. -/
def redc : Prog isa :=
  .seq (.block redcSetup) (.seq (.loop redcRow .ne) (.block redcFinish))

/-- Montgomery square using one copy of each off-diagonal product. -/
def montSquare (o a : Nat) : Prog isa :=
  .seq (rawSquare a) (.seq redc (.seq (.block [.mov .r10 (.mem (hdr (sArr Public.aN)))]) (Adx.finish o)))

/-- Equal input arrays use the square kernel; other products retain the
fused ADX multiplication. The size guard preserves its small-size fallback. -/
def montMul (o a b : Nat) : Prog isa :=
  if a = b then .seq (.block Adx.sizeTest)
    (.ite .e (montSquare o a) (Adx.montMulAdx o a b))
  else Adx.montMulAdx o a b

end VG.Impl.Bignum.X86_64.AdxSquare
