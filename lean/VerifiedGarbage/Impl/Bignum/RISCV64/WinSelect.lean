module

public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked

/-!
# Selecting an entry of a 16-entry table on RISC-V

`winSelect o t`: array `o` := array `t + d`, for the secret digit `d < 16` in
`t6`, in a working space of the public-key operation's layout
(`PublicChecked.lean`: `a7` array 0's base, `s5` an array's size, `t0` `w`),
in one pass over the sixteen arrays from `t`, all of them read whatever `d`
is.

The masks are computed once (`masks`): one register for each value of the
digit's low three bits, all ones for `d mod 8`'s and 0 for the others, and
one for its top bit. Then, two columns (words) at a time, the entries below 8
and those from 8 are each reduced to one by `and`s and `or`s under the same
eight masks (`half`), and the top bit's mask picks one of the two (`merge`).
A last odd column takes the word above the number along, within the arrays'
`w + 2` words.

Registers: the masks `a0`–`a6` and `t2`, and `s4` the top bit's; `t3` the
pointer into the table, `t4` the output's, `t5` the pairs of columns left;
`s0`, `s1` and `s2`, `s3` the two halves' words, `t6` the word loaded.
-/

@[expose] public section

namespace VG.Impl.Bignum.RISCV64.WinSelect

open VG.RISCV64 VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-- The mask of the entries `j` and `8 + j`. -/
def maskReg (j : Nat) : Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .t2].getD j .a0

/-- `t4 := 2^(d mod 8)`. -/
def hot : List Instr := [.logicImm .and .t5 .t6 7, .li .t4 1, .shiftReg .sll .d .t4 .t4 .t5]

/-- `r :=` all ones if bit `j` of `t4` is set, else 0. -/
def bitMask (r : Reg) (j : Nat) : List Instr := [.shift .sll .d r .t4 (63 - j), .shift .sra .d r r 63]

/-- The masks of the digit in `t6`. -/
def masks : List Instr :=
  [.shift .sll .d .s4 .t6 60, .shift .sra .d .s4 .s4 63] ++ hot ++
    (List.range 8).flatMap (fun j => bitMask (maskReg j) j)

/-- The pointers and the count, `⌈w / 2⌉`. -/
def bases (o t : Nat) : List Instr :=
  base .t3 t ++ base .t4 o ++ [.addi .t5 .t0 1, .shift .srl .d .t5 .t5 1]

/-- The first entry's two words under the mask `m` into `x` and `y`; the
pointer at the next entry. -/
def first (x y m : Reg) : List Instr :=
  [.load .d x .t3 0, .logic .and x x m, .load .d y .t3 8, .logic .and y y m, .add .t3 .t3 .s5]

/-- An entry's two words under the mask `m` or'ed into `x` and `y`; the
pointer at the next entry. -/
def cell (x y m : Reg) : List Instr :=
  [.load .d .t6 .t3 0, .logic .and .t6 .t6 m, .logic .or x x .t6,
    .load .d .t6 .t3 8, .logic .and .t6 .t6 m, .logic .or y y .t6, .add .t3 .t3 .s5]

/-- The entries from 1 to `n` of eight, after the first. -/
def cells (x y : Reg) (n : Nat) : List Instr :=
  (List.range n).flatMap fun j => cell x y (maskReg (j + 1))

/-- Eight entries' two words into `x` and `y`. -/
def half (x y : Reg) : List Instr := first x y (maskReg 0) ++ cells x y 7

/-- The low or the high half's words, by the top bit's mask, into `s0` and
`s1`. -/
def merge : List Instr :=
  [.logic .xor .s2 .s2 .s0, .logic .and .s2 .s2 .s4, .logic .xor .s0 .s0 .s2,
    .logic .xor .s3 .s3 .s1, .logic .and .s3 .s3 .s4, .logic .xor .s1 .s1 .s3]

/-- Store the two words, and the pointers at the next two columns. -/
def next : List Instr :=
  [.store .d .s0 .t4 0, .store .d .s1 .t4 8, .addi .t4 .t4 16,
    .shift .sll .d .t6 .s5 4, .sub .t3 .t3 .t6, .addi .t3 .t3 16]

/-- Array `o` := array `t + d`, for `d < 16` in `t6`. -/
def winSelect (o t : Nat) : Prog isa :=
  .seq (.block (masks ++ bases o t))
    (countLoop .t5 (half .s0 .s1 ++ (half .s2 .s3 ++ (merge ++ next))))

end VG.Impl.Bignum.RISCV64.WinSelect
