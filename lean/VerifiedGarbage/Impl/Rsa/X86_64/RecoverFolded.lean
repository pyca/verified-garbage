module

public import VerifiedGarbage.Impl.Rsa.X86_64.Recover

/-! # Prime recovery with the trailing squarings inside the exponentiation

The root is captured in array 15. Its two padding words hold the active
and found masks. The accumulator always advances, and a nonzero window
digit resets these masks. Two final squares complete the chain, with the
second enabled only when the secret alignment shift is two.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.Keys.Recover.Folded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

def aRoot : Nat := 15

/-! Preserve the unsplit exponent across the existing, proved computation of
its trailing-zero count. This keeps the preparation independent of the
candidate loop while the folded implementation is developed. -/

def copyExponent (o a : Nat) : Prog isa :=
  .seq (.block (ws ++ base a .rsi ++ base o .rbx))
    (.seq (.block [.alu .add .r12 (.imm 2), .alu .add .r12 (.reg .r12)]) copyWords)

def halfTail : Prog isa := .seq (wordLoop 0 shrBody) (wordLoop 0 selBody)

def halfOnce : Prog isa := .seq (.block halfHead) halfTail

/-- Keep the first half when t is odd; otherwise halve a second time. -/
def halfAlign : Prog isa :=
  .seq (.block (halfHead ++ [.mov .rax (.mem (hdr sT)), .alu .and .rax (.imm 1),
    .mov32 .rbp (.imm 0), .alu .sub .rbp (.reg .rax)])) halfTail

def storeSigma : List Instr :=
  [.mov .rax (.mem (hdr sT)), .alu .and .rax (.imm 1), .alu .xor .rax (.imm 1),
    .alu .add .rax (.imm 1), .store (hdr sT) .rax]

/-- E = (d e - 1) / 2^sigma, with sigma in {1,2} and t - sigma even. -/
def prepare : Prog isa :=
  seqs [copyExponent aG aM, halving, copyExponent aM aG, halfOnce, halfAlign, .block storeSigma]

def active : MemOp := ix .r8 .r12
def found : MemOp := ix .r8 .r12 8

/-- The suffix can disable a square's capture without changing its work. -/
def enabled : Option Nat → List Instr
  | none => [.mov .r15 (.imm (BitVec.ofInt 32 (-1)))]
  | some j => [.mov32 .rax (.imm (BitVec.ofNat 32 j)), .alu .cmp .rax (.mem (hdr sT)),
      .alu .sbb .r15 (.reg .r15)]

/-- Record a root if the live square became 1, and stop tracking at ±1.
`sMask` holds the equality mask for 1; `rbp = 0` iff the square is -1.
Leave the inverse capture mask in `rbp`, for `selBody`. -/
def captureCore : List Instr :=
  [.mov .rcx (.mem active), .alu .and .r15 (.reg .rcx),
    .mov .rax (.mem (hdr sMask)), .mov .rbp (.reg .rax), .alu .and .rbp (.reg .r15),
    .mov .r11 (.mem found), .alu .or .r11 (.reg .rbp), .store found .r11,
    .alu .or .rdx (.reg .rax), .alu .and .rdx (.reg .r15),
    .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rcx (.reg .rdx), .store active .rcx,
    .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]

def captureMasks (j : Option Nat) : List Instr :=
  ([.alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr) ++
  ws ++ base aRoot .r8 ++ base aY .rsi ++ enabled j ++ captureCore

/-- Advance the accumulator regardless of whether a root was captured. -/
def comparisons (a : Nat) : Prog isa :=
  seqs (eqA a aO ++ [.block (eqStore sMask)] ++ eqA a aNg)

def capturePrefix (j : Option Nat) : Prog isa :=
  .seq (.block (captureMasks j)) (wordLoop 0 selBody)

def capture (j : Option Nat) : Prog isa :=
  .seq (capturePrefix j) (copyA aY aX)

def square (mul : Nat → Nat → Nat → Prog isa) (j : Option Nat) : Prog isa :=
  seqs [mul aX aY aY, comparisons aX, capture j]

/-- Reset the tracking flags after a nonzero digit. -/
def resetCore : List Instr :=
  [.alu .or .rdx (.mem (hdr sMask)), .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))),
    .mov .rax (.mem (hdr sC2)), .shift .shr .rax 62, .alu .cmp .rax (.imm 1), .alu .sbb .r15 (.reg .r15),
    .mov .rcx (.mem found), .alu .and .rcx (.reg .r15), .store found .rcx,
    .mov .rcx (.mem active), .alu .and .rcx (.reg .r15),
    .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))), .alu .and .rdx (.reg .r15),
    .alu .or .rcx (.reg .rdx), .store active .rcx]

def resetMasks : List Instr :=
  ([.alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr) ++
  ws ++ base aRoot .r8 ++ resetCore

def reset : Prog isa := .seq (comparisons aY) (.block resetMasks)

def windowArithmetic (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs [windowSelect, square mul none, square mul none, mul aY aY aXm, reset]

def window (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (windowArithmetic mul) (.block windowNext)

def paddedScan (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block expInit)
    (.loop (.seq (.block wordHead) (.seq (.loop (window mul) .ne) (.block wordNext))) .ne)

def windows (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (zeroA aRoot) (paddedScan mul)

/-- Copy the root out of its capture buffer and expose only the found mask. -/
def finish : Prog isa :=
  .seq (copyA aY aRoot) (.block (ws ++ base aRoot .r8 ++
    ([.mov .rax (.mem found), .store (hdr sC3) .rax] : List Instr)))

def suffix (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (square mul none) (square mul (some 1))

def exponentiate (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs [windowPowers mul, windows mul, suffix mul, finish]

def candidate (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs [.block gBlk, setWord aX .rcx, mul aXm aX aR2, copyA aG aXm, copyA aY aO, exponentiate mul]

def candBody (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (candidate mul) (.block candNext)

def candLoop (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (hdr sCand) .rax]) (.loop (candBody mul) .ne)

def rest (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs ([prepare] ++ mont mul ++ [candLoop mul] ++ fin mul)

def main (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs ([.block CrtValues.head] ++ loadA aN sN sK ++ loadA aE sE sElen ++ loadA aD sD sDl ++
    [.block minvBlk] ++ prod ++
    [.block skipBlk, wordLoop 0 orBody, .block skipTest, .ite .ne fail (rest mul)])

def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid))
    (.ite .ne fail (main mul))

end VG.Impl.Rsa.X86_64.Keys.Recover.Folded
