module

public import VerifiedGarbage.Impl.Aes.RISCV64.Linear

/-!
# The layers of bitsliced AES on RISC-V

Four blocks in eight 64-bit slices: bit `j` of the byte in row `r` and column
`c` of block `k` is at bit `k + 4 (c + 4 r)` of slice `j` (`toBs`), so rows
are rotated by rotating the words by 16 bits. RV64I has no rotate: that is
two shifts and an XOR.

The masks are in slots of the scratch buffer: those of `toBs`'s exchanges,
by the index bit, from slot `bsSlot` on, and the linear layers' from `srSlot`.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64

/-! ## Masks -/

def bsSlot : Nat := 52
def srSlot : Nat := 64

/-- Masks of the positions whose index bit of place value `2 ^ (k - 1)` is 0. -/
def idxMasks : List (Nat × BitVec 64) :=
  [(1, 0x5555555555555555), (2, 0x3333333333333333), (3, 0x0F0F0F0F0F0F0F0F),
   (4, 0x00FF00FF00FF00FF), (5, 0x0000FFFF0000FFFF), (6, 0x00000000FFFFFFFF)]

/-- ShiftRows': the low bytes of rows 2 and 3, and rows 1 and 3. -/
def srMasks : List (Nat × BitVec 64) := [(1, 0x00FF00FF00000000), (2, 0xFFFF0000FFFF0000)]

/-! ## Bytes to slices -/

/-- Exchange bit `b` of the register's number with bit `i` of the position. -/
def exch (b i : Nat) : List Instr := ldS t1 (bsSlot + i) :: exchange b i t0 t1

/-- From the halves of four blocks (`q (k + 4 c)`: columns `2 c` and `2 c + 1`
of block `k`) to slices. -/
def toBs : List Instr := exch 2 3 ++ exch 2 4 ++ exch 2 5 ++ exch 2 2 ++ exch 1 1 ++ exch 0 0

/-- And back. -/
def fromBs : List Instr := exch 0 0 ++ exch 1 1 ++ exch 2 2 ++ exch 2 5 ++ exch 2 4 ++ exch 2 3

/-! ## ShiftRows -/

/-- Rows 2 and 3 of slice `a` rotated by two columns. -/
def srTwo (a : Reg) : List Instr :=
  [shrI t0 a 8, xorR t0 t0 a, andR t0 t0 .t3, xorR a a t0, shlI t0 t0 8, xorR a a t0]

/-- Rows 1 and 3 of slice `a` rotated by one column: their bits, moved, that
leave these rows are masked off. -/
def srOne (a : Reg) (l r : Nat) : List Instr :=
  [andR t0 a .t4, xorR a a t0, shrI t1 t0 r, shlI t0 t0 l, xorR t0 t0 t1, andR t0 t0 .t4, xorR a a t0]

def shiftRows : List Instr :=
  [ldS .t3 srSlot, ldS .t4 (srSlot + 1)] ++
    (List.range 8).flatMap fun j => srTwo (q j) ++ srOne (q j) 12 4

def invShiftRows : List Instr :=
  [ldS .t3 srSlot, ldS .t4 (srSlot + 1)] ++
    (List.range 8).flatMap fun j => srTwo (q j) ++ srOne (q j) 4 12

/-! ## MixColumns -/

/-- Where MixColumns keeps slice `j` of `b = a ⊕ next(a)`, and of `next(a)`, the
next row's bytes, while it needs them. -/
def mb (j : Nat) : Reg := if j = 7 then .t2 else if j % 2 = 0 then .t3 else .t4
def mn (j : Nat) : Reg := if j % 2 = 0 then .t5 else .t6

/-- `next(a)` and `b` of slice `j`. -/
def mcNext (j : Nat) : List Instr :=
  [shrI t0 (q j) 16, shlI t1 (q j) 48, xorR (mn j) t0 t1, xorR (mb j) (q j) (mn j)]

/-- The result's slice `j`: `2 b ⊕ next(a) ⊕ row2(b)`. -/
def mcOut (j : Nat) : List Instr :=
  [shrI t0 (mb j) 32, shlI t1 (mb j) 32, xorR t0 t0 t1, xorR (q j) t0 (mn j)] ++
    (if j = 0 then [] else [xorR (q j) (q j) (mb (j - 1))]) ++
    (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [xorR (q j) (q j) (mb 7)] else [])

/-- Slice 7 first: slice `j`'s `b` is needed for the slice above. -/
def mixColumns : List Instr :=
  mcNext 7 ++ mcNext 6 ++ mcOut 7 ++ mcNext 5 ++ mcOut 6 ++ mcNext 4 ++ mcOut 5 ++ mcNext 3 ++
    mcOut 4 ++ mcNext 2 ++ mcOut 3 ++ mcNext 1 ++ mcOut 2 ++ mcNext 0 ++ mcOut 1 ++ mcOut 0

/-- Where `imcPre` keeps its sums. -/
def ib : Nat → Reg
  | 0 => .t2 | 1 => .t3 | 2 => .t4 | 3 => .t5
  | 4 => .t6 | 5 => .a6 | 6 => .a7 | _ => .s8

/-- `a ⊕ 4 (a ⊕ row2(a))`, whose MixColumns is InvMixColumns of `a`:
`d(x) = a(x) (4 x² + 5) mod x⁴ + 1`. `ib j` holds slice `j` of `a ⊕ row2(a)`,
and `t0` the sum of its slices 6 and 7, which the reduction needs twice. -/
def imcPre : List Instr :=
  ((List.range 8).flatMap fun j =>
    [shrI t0 (q j) 32, shlI t1 (q j) 32, xorR t0 t0 t1, xorR (ib j) (q j) t0]) ++
  [xorR t0 (ib 6) (ib 7),
   xorR (q 0) (q 0) (ib 6), xorR (q 1) (q 1) t0,
   xorR (q 2) (q 2) (ib 0), xorR (q 2) (q 2) (ib 7),
   xorR (q 3) (q 3) (ib 1), xorR (q 3) (q 3) (ib 6),
   xorR (q 4) (q 4) (ib 2), xorR (q 4) (q 4) t0,
   xorR (q 5) (q 5) (ib 3), xorR (q 5) (q 5) (ib 7),
   xorR (q 6) (q 6) (ib 4), xorR (q 7) (q 7) (ib 5)]

def invMixColumns : List Instr := imcPre ++ mixColumns

/-! ## AddRoundKey -/

/-- The round key at `kp`, a doubleword a slice. -/
def addRoundKey : List Instr :=
  (List.range 8).flatMap fun j => [.load .d t0 kp (8 * j), xorR (q j) (q j) t0]

end VG.Impl.Aes.RISCV64
