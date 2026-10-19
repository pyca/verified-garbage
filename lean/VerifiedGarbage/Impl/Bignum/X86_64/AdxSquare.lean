module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareWide
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareGrouped

/-! ADX squaring and Montgomery reduction. -/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.AdxSquare
open VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Adx

/-- Store a row's final carry and advance the public row index and window. -/
def crossTail : List Instr :=
  [.store (ix .r8 .r14) .rcx, .alu .add .r8 (.imm 8), .alu .add .rbp (.imm 1),
    .alu .cmp .rbp (.reg .r10)]

/-- Row `i` adds `a_i` times `a_0, …, a_{i-1}` at word `i` of the product,
by the multiply-add `row` (`r8 += rdx · [r9]` over `rbp` words, its carry
word in `rcx`). Only products strictly below the diagonal are accumulated. -/
def crossRowWith (row : Prog isa) : Prog isa :=
  .seq (.block [.mov .rdx (.mem (ix .r9 .rbp))])
    (.seq row (.block crossTail))

def crossRow : Prog isa := crossRowWith AdxSquareWide.generalRow

/-- Clear the product buffer, then accumulate its off-diagonal products, by
the rows `crossRowWith row`. `r8` addresses `2 w + 2` words; `r9` addresses
the input; `rbx = w ≥ 2`. -/
def crossWith (row : Prog isa) : Prog isa :=
  .seq Adx.zeroWin (.seq (.block [.mov .r10 (.reg .rbx), .mov32 .rbp (.imm 1), .alu .add .r8 (.imm 8)])
    (.loop (crossRowWith row) .ne))

def cross : Prog isa := crossWith AdxSquareWide.generalRow

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

/-- Process one pair of cross-product words and one diagonal product, by
`core` (`diagonalCore`'s result from its registers). -/
def diagonalStepWith (core : List Instr) : Prog isa :=
  .seq (.block diagonalHead) (.seq (.block core) (.block diagonalTail))

def diagonalStep : Prog isa := diagonalStepWith diagonalCore

/-- Double the cross products and add every diagonal square, by the steps
`diagonalStepWith core`. `r10 = w > 0`, `r8` is the product buffer and `r9`
the input. -/
def diagonalWith (core : List Instr) : Prog isa :=
  .seq (.block [.mov32 .r15 (.imm 0), .mov32 .rbp (.imm 0), .mov32 .r14 (.imm 0)])
    (.loop (diagonalStepWith core) .ne)

def diagonal : Prog isa := diagonalWith diagonalCore

/-- Groups of eight, or of four, keep both carries live; all other sizes
retain the general loop. -/
def diagonalChoice : Prog isa :=
  .seq (.block [.mov .rax (.reg .r10), .alu .and .rax (.imm 7), .alu .cmp .rax (.imm 0)])
    (.ite .e AdxSquareGrouped.diagonal8
      (.seq (.block [.mov .rax (.reg .r10), .alu .and .rax (.imm 3), .alu .cmp .rax (.imm 0)])
        (.ite .e AdxSquareGrouped.diagonal diagonal)))

/-- The unreduced square, at `aAcc + 16`, using the adjacent `aAcc` and
`aTmp` storage, with the diagonal `diag`. Each off-diagonal product is
computed only once. -/
def rawSquareWith (diag : Prog isa) (a : Nat) : Prog isa :=
  .seq (.block (Adx.setup a)) (.seq cross
    (.seq (.block (Adx.setup a)) (.seq (.block [.mov .r10 (.reg .rbx)]) diag)))

def rawSquare (a : Nat) : Prog isa := rawSquareWith diagonalChoice a

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

/-- One Montgomery cancellation row, by `head` (the multiplier into `rdx`, as
`redcHead`) and the multiply-add `row`. `r9` is the modulus, `rbp` its
length, `r8` the moving window and `r10` the pending high carry. -/
def redcRowWith (head : List Instr) (row : Prog isa) : Prog isa :=
  .seq (.block head) (.seq row (.seq (.block redcTail) (.block Adx.rowEnd)))

def redcRow : Prog isa := redcRowWith redcHead AdxSquareWide.row

def redcSetup : List Instr :=
  [.mov .r8 (.mem (hdr (sArr Public.aAcc))), .alu .add .r8 (.imm 16),
    .mov .r9 (.mem (hdr (sArr Public.aN))), .mov .rbp (.mem (hdr sW)), .mov32 .r10 (.imm 0)]

/-- Materialize the last row's high carry in the result's padding words. -/
def redcFinish : List Instr :=
  [.store (ix .r8 .rbp) .r10, .mov32 .rax (.imm 0), .store (ix .r8 .rbp 8) .rax]

/-- Montgomery reduction of the `2 w` words at `aAcc + 16`, by the rows
`redcRowWith head row`. -/
def redcWith (head : List Instr) (row : Prog isa) : Prog isa :=
  .seq (.block redcSetup) (.seq (.loop (redcRowWith head row) .ne) (.block redcFinish))

def redc : Prog isa := redcWith redcHead AdxSquareWide.row

def redcTest : List Instr :=
  [.mov .rax (.mem (hdr sW)), .alu .and .rax (.imm 7), .alu .cmp .rax (.imm 0)]

/-- Eight-word tiles for aligned sizes, with the general-size reduction retained. -/
def redcChoice : Prog isa :=
  .seq (.block redcTest) (.ite .e AdxRotate8.redc redc)

/-- Montgomery square using one copy of each off-diagonal product, with the
diagonal `diag` and the reduction `red`. -/
def montSquareWith (diag red : Prog isa) (o a : Nat) : Prog isa :=
  .seq (rawSquareWith diag a)
    (.seq red (.seq (.block [.mov .r10 (.mem (hdr (sArr Public.aN)))]) (Adx.finish o)))

def montSquare (o a : Nat) : Prog isa := montSquareWith diagonalChoice redcChoice o a

/-- `montSquare` for `w` a multiple of 4 but not of 8, which takes the
four-word diagonal and the general reduction. -/
def montSquare4 (o a : Nat) : Prog isa := montSquareWith AdxSquareGrouped.diagonal redc o a

/-- Equal input arrays use the square kernel; other products retain the
fused ADX multiplication. The size guard preserves its small-size fallback. -/
def montMul (o a b : Nat) : Prog isa :=
  if a = b then .seq (.block Adx.sizeTest)
    (.ite .e (montSquare o a) (Adx.montMulAdx o a b))
  else Adx.montMulAdx o a b

end VG.Impl.Bignum.X86_64.AdxSquare
