module

public import VerifiedGarbage.Impl.Aes.RISCV64.Rounds

/-!
# Bitsliced AES on RISC-V, with ShiftRows left out

**ShiftRows is not done.** A round that leaves every byte where it is leaves
the byte of row `r` and column `c` at column `c + r` (form 1 of the state,
where form 0 is the plain one), which the next layers allow for: MixColumns
of form 1 (`mixColumns1`) takes the next row's byte one column further, and
the round key is stored in form 1. The round after does ShiftRows twice
(`sr2`: only the odd rows move, by two columns), which gives form 0 again.
The numbers of rounds are even, so odd rounds end in form 1 and even ones in
form 0. The inverse cipher's rounds go the other way: its first starts with
`sr2`, which from form 0 gives InvShiftRows in form 1, and the second with
nothing, which gives form 0.

**The S-box's constant is in the round keys.** `{63}` in every byte goes
through ShiftRows and MixColumns unchanged (`2 + 3 + 1 + 1 = 1`), so the
round keys but the first have it added, and the rounds use `sbox0Code`,
which leaves it out; likewise `invSbox0Code` takes its input with it added.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64

/-! ## Masks -/

def fxSlot : Nat := 66

/-- The low three columns of every row, and the low bytes of the odd rows. -/
def fxMasks : List (Nat × BitVec 64) := [(1, 0x0FFF0FFF0FFF0FFF), (2, 0x00FF000000FF0000)]

/-! ## ShiftRows twice -/

def sr2One (a : Reg) : List Instr :=
  [shrI t0 a 8, xorR t0 t0 a, andR t0 t0 .a6, xorR a a t0, shlI t0 t0 8, xorR a a t0]

/-- The odd rows rotated by two columns. -/
def sr2 : List Instr := ldS .a6 (fxSlot + 1) :: (List.range 8).flatMap fun j => sr2One (q j)

/-! ## MixColumns of form 1 -/

/-- `mn j` the next row's bytes, one column on, and `mb j` those and slice
`j`'s own. The columns of every row are rotated by one (the mask in `a6`),
and then the rows. -/
def mcNext1 (j : Nat) : List Instr :=
  [shrI t0 (q j) 4, shlI t1 (q j) 12, xorR t0 t0 t1, andR t0 t0 .a6, xorR t0 t0 t1,
   shrI t1 t0 16, shlI t0 t0 48, xorR (mn j) t0 t1, xorR (mb j) (q j) (mn j)]

/-- The bytes two rows and two columns on from `d`'s, to `d` (the mask in `a7`). -/
def row2 (d a e : Reg) (k : Reg) : List Instr :=
  [shrI d a 32, shlI e a 32, xorR d d e, shrI e d 8, shlI d d 8, xorR e e d, andR e e k, xorR d d e]

def mcOut1 (j : Nat) : List Instr :=
  row2 t0 (mb j) t1 .a7 ++ [xorR (q j) t0 (mn j)] ++
    (if j = 0 then [] else [xorR (q j) (q j) (mb (j - 1))]) ++
    (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [xorR (q j) (q j) (mb 7)] else [])

def mixColumns1 : List Instr :=
  [ldS .a6 fxSlot, ldS .a7 (bsSlot + 3)] ++
  mcNext1 7 ++ mcNext1 6 ++ mcOut1 7 ++ mcNext1 5 ++ mcOut1 6 ++ mcNext1 4 ++ mcOut1 5 ++
    mcNext1 3 ++ mcOut1 4 ++ mcNext1 2 ++ mcOut1 3 ++ mcNext1 1 ++ mcOut1 2 ++ mcNext1 0 ++
    mcOut1 1 ++ mcOut1 0

/-- `imcPre` of form 1 (the mask in `s10`). -/
def imcPre1 : List Instr :=
  ldS .s10 (bsSlot + 3) ::
  ((List.range 8).flatMap fun j => row2 t0 (q j) t1 .s10 ++ [xorR (ib j) (q j) t0]) ++ imcSum

def invMixColumns1 : List Instr := imcPre1 ++ mixColumns1

/-! ## A round key to slices -/

/-- `swapMove` of two equal words, both in `lo`. -/
def swapDup (lo hi t k : Reg) (n : Nat) : List Instr :=
  [shrI t lo n, xorR t t lo, andR t t k, xorR hi lo t, shlI t t n, xorR lo lo t]

/-- `toBs` of a block four times over, from its halves in `q 0` and `q 4`. -/
def slice1 : List Instr :=
  [ldS t1 (bsSlot + 3)] ++ swapMove (q 0) (q 4) t0 t1 8 ++
  [ldS t1 (bsSlot + 4)] ++ swapMove (q 0) (q 4) t0 t1 16 ++
  [ldS t1 (bsSlot + 5)] ++ swapMove (q 0) (q 4) t0 t1 32 ++
  [ldS t1 (bsSlot + 2)] ++ swapMove (q 0) (q 4) t0 t1 4 ++
  [ldS t1 (bsSlot + 1)] ++ swapDup (q 0) (q 2) t0 t1 2 ++ swapDup (q 4) (q 6) t0 t1 2 ++
  [ldS t1 bsSlot] ++ swapDup (q 0) (q 1) t0 t1 1 ++ swapDup (q 2) (q 3) t0 t1 1 ++
    swapDup (q 4) (q 5) t0 t1 1 ++ swapDup (q 6) (q 7) t0 t1 1

end VG.Impl.Aes.RISCV64
