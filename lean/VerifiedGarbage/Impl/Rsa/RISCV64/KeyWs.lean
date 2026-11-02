module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul

/-!
# The working space of the RSA key operations on RISC-V

The key operations (`vg_rsa_crt_values`, `vg_rsa_check_key` and
`vg_rsa_check_crt_key`) keep their numbers in the caller's working space, as
on PPC64LE (`Impl/Rsa/PPC64LE/KeyWs.lean`) but in words of 64 bits: a header
of `hdr` bytes, then arrays of `w + 2` words, array `j` at byte `hdr + j S`
with the stride `S = 8 (w + 2)`. Numbers are `w` words, least significant
first; the words after them are the division's extra word and the halving's
incoming word. There is no carry bit: a borrow is computed with `sltu`.

The header's bytes 0–95 hold the caller's `s0`–`s11` (`saveRegs`), and the
slots from byte 128 on are words holding 0 or 1.

The base `B` is in `s11`, the stride in `s10` and `w` in `s9`, which the
operations here leave alone: they compute every address from them (`ptr`),
so their addresses and branches depend only on `w` and `B`. The word loops
use `t0`–`t2` (the pointers), `t3` (the count), `t4` (the borrow, the carry
or a mask), `t5`, `t6` and `a4` (temporaries):

* `sub3 o a b`: `[o] := [a] - [b]` modulo `2^(64 w)`, the borrow in `t4`.
* `sel o a b sl`: `[o] := [b]` if the slot `sl` holds 1, `[a]` if it holds 0.
* `copy o a`: `[o] := [a]`.
* `half j`: `[j] := ([j] + t4 · 2^(64 w)) / 2`, for `t4` 0 or 1.
* `eqS d a b`: the slot `d` := 1 if `[a] = [b]`, 0 otherwise.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.Keys

open VG.RISCV64 VG.Impl.Bignum.RISCV64

/-- Right-nested sequencing. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- `mv d, n`. -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The header's size in bytes: the arrays start there. -/
def hdr : Nat := 256

/-- Slots of the shared routines (a word each). -/
def sOdd : Nat := 128
def sB : Nat := 136
def sC : Nat := 144

/-- The caller's callee-saved registers, saved at the header's word `i`: `s11`,
which keeps the base, last. -/
def saved (i : Nat) : Reg :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11].getD i .s0

/-- The working space, the stack argument at `sp + off`, into `t0`; the
registers saved there, and its address into `s11`. -/
def save (off : Nat) : List Instr :=
  [.addSp .t0 0, .load .d .t0 .t0 off] ++
  (List.range 12).flatMap (fun i => [.store .d (saved i) .t0 (8 * i)]) ++ [mov .s11 .t0]

/-- The registers back, through `s11`, which is restored last. -/
def restore : List Instr :=
  (List.range 11).flatMap (fun i => [.load .d (saved i) .s11 (8 * i)]) ++
    [.load .d .s11 .s11 (8 * 11)]

/-- `r` := the address of array `j`, `B + hdr + j S`. -/
def ptr (r : Reg) (j : Nat) : List Instr :=
  [.li r j, .mul r r .s10, .add r r .s11, .addi r r hdr]

/-- The three pointers of an operation `[o] := f [a] [b]`. -/
def ptrs (o a b : Nat) : List Instr := ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b

/-- `s9 := w = ⌈len / 8⌉` and `s10 := 8 (w + 2)`, the stride. -/
def setW (len : Reg) : List Instr :=
  [.addi .s9 len 7, .shift .srl .d .s9 .s9 3, .addi .s10 .s9 2, .shift .sll .d .s10 .s10 3]

/-- One word of `[a] - [b]`, the borrow in and out in `t4`, to `[o]`. -/
def subBody : List Instr :=
  [.load .d .t5 .t1 0, .load .d .t6 .t2 0, .sltu .a4 .t5 .t6, .sub .t5 .t5 .t6,
    .sltu .t6 .t5 .t4, .sub .t5 .t5 .t4, .logic .or .t4 .a4 .t6, .store .d .t5 .t0 0,
    .addi .t0 .t0 8, .addi .t1 .t1 8, .addi .t2 .t2 8]

/-- `[o] := [a] - [b]` over `w + x` words, the borrow out in `t4`. -/
def subN (x : Int) (o a b : Nat) : Prog isa :=
  .seq (.block (ptrs o a b ++ [.addi .t3 .s9 x, .li .t4 0])) (countLoop .t3 subBody)

/-- `[o] := [a] - [b]` modulo `2^(64 w)`, the borrow out in `t4`. -/
def sub3 (o a b : Nat) : Prog isa := subN 0 o a b

/-- One word of `mask ? [b] : [a]`, the mask in `t4`, to `[o]`. -/
def selBody : List Instr :=
  [.load .d .t5 .t1 0, .load .d .t6 .t2 0, .logic .xor .t6 .t6 .t5, .logic .and .t6 .t6 .t4,
    .logic .xor .t6 .t6 .t5, .store .d .t6 .t0 0, .addi .t0 .t0 8, .addi .t1 .t1 8,
    .addi .t2 .t2 8]

/-- `[o] := [b]` if the slot `sl` holds 1, else `[a]`. -/
def sel (o a b sl : Nat) : Prog isa :=
  .seq (.block (ptrs o a b ++ [.load .d .t4 .s11 sl, .li .t5 0, .sub .t4 .t5 .t4, mov .t3 .s9]))
    (countLoop .t3 selBody)

/-- One word of `[a]` to `[o]`. -/
def copyBody : List Instr :=
  [.load .d .t5 .t1 0, .store .d .t5 .t0 0, .addi .t0 .t0 8, .addi .t1 .t1 8]

/-- `[o] := [a]`. -/
def copy (o a : Nat) : Prog isa :=
  .seq (.block (ptr .t0 o ++ ptr .t1 a ++ [mov .t3 .s9])) (countLoop .t3 copyBody)

/-- One word of the halving: the word at `t0` := its upper 63 bits and the
low bit of the next word. -/
def halfBody : List Instr :=
  [.load .d .t5 .t0 0, .load .d .t6 .t0 8, .shift .sll .d .t6 .t6 63, .shift .srl .d .t5 .t5 1,
    .logic .or .t5 .t5 .t6, .store .d .t5 .t0 0, .addi .t0 .t0 8]

/-- `[j] := ([j] + t4 · 2^(64 w)) / 2`: `t4` stored as word `w`, then the shift. -/
def half (j : Nat) : Prog isa :=
  .seq (.block (ptr .t0 j ++ [.shift .sll .d .t5 .s9 3, .add .t5 .t0 .t5, .store .d .t4 .t5 0,
      mov .t3 .s9]))
    (countLoop .t3 halfBody)

/-- The slot `sl` := the low bit of `[j]`. -/
def bitOf (sl j : Nat) : List Instr :=
  ptr .t0 j ++ [.load .d .t5 .t0 0, .logicImm .and .t5 .t5 1, .store .d .t5 .s11 sl]

/-- The borrow (`t4`) to the slot `sl`. -/
def stBorrow (sl : Nat) : List Instr := [.store .d .t4 .s11 sl]

/-- The slot `d` := the slots `a` and `b` and'ed. -/
def andS (d a b : Nat) : List Instr :=
  [.load .d .t5 .s11 a, .load .d .t6 .s11 b, .logic .and .t5 .t5 .t6, .store .d .t5 .s11 d]

/-- The low word of `[j]` := 1. -/
def setOne (j : Nat) : List Instr := ptr .t0 j ++ [.li .t5 1, .store .d .t5 .t0 0]

/-- The low bit of `[j]` set. -/
def orOne (j : Nat) : List Instr :=
  ptr .t0 j ++ [.load .d .t5 .t0 0, .logicImm .or .t5 .t5 1, .store .d .t5 .t0 0]

/-- The low bit of `[j]` cleared. -/
def clrLow (j : Nat) : List Instr :=
  ptr .t0 j ++ [.load .d .t5 .t0 0, .logicImm .and .t5 .t5 (-2), .store .d .t5 .t0 0]

/-- One word of the comparison: `t4 |= [a] ^ [b]`. -/
def eqBody : List Instr :=
  [.load .d .t5 .t1 0, .load .d .t6 .t2 0, .logic .xor .t5 .t5 .t6, .logic .or .t4 .t4 .t5,
    .addi .t1 .t1 8, .addi .t2 .t2 8]

/-- The slot `d` := 1 if `[a] = [b]`, else 0: the words' differences or'ed
into `t4`, which is 0 exactly when they are equal, then `1 - (0 <u t4)`. -/
def eqS (d a b : Nat) : Prog isa :=
  .seq (.block (ptr .t1 a ++ ptr .t2 b ++ [.li .t4 0, mov .t3 .s9]))
    (.seq (countLoop .t3 eqBody)
      (.block [.li .t5 0, .sltu .t5 .t5 .t4, .logicImm .xor .t5 .t5 1, .store .d .t5 .s11 d]))

/-- The `c` arrays from array 0 on := 0. -/
def zeroArrays (c : Nat) : Prog isa :=
  .seq (.block [.li .t3 c, .mul .t3 .t3 .s10, .shift .srl .d .t3 .t3 3, .addi .t0 .s11 hdr, .li .t5 0])
    (countLoop .t3 [.store .d .t5 .t0 0, .addi .t0 .t0 8])

/-- `[j] :=` the `len` bytes at `src`, most significant first: byte `i` is
byte `len - 1 - i` of the number, which is little-endian in memory. -/
def load (j : Nat) (src len : Reg) : Prog isa :=
  .seq (.block ([mov .t1 src, mov .t3 len] ++ ptr .t0 j ++ [.add .t0 .t0 .t3, .addi .t0 .t0 (-1)]))
    (countLoop .t3 [.load .b .t5 .t1 0, .store .b .t5 .t0 0, .addi .t1 .t1 1, .addi .t0 .t0 (-1)])

/-- `[j]`'s low `len` bytes to `dst`, most significant first, masked by `t4`. -/
def storeBytes (j : Nat) (dst len : Reg) : Prog isa :=
  .seq (.block (ptr .t1 j ++ [.add .t1 .t1 len, .addi .t1 .t1 (-1), mov .t0 dst, mov .t3 len]))
    (countLoop .t3 [.load .b .t5 .t1 0, .logic .and .t5 .t5 .t4, .store .b .t5 .t0 0,
      .addi .t0 .t0 1, .addi .t1 .t1 (-1)])

/-- `len` zero bytes to `dst`. -/
def zeroBytes (dst len : Reg) : Prog isa :=
  .seq (.block [mov .t0 dst, mov .t3 len, .li .t5 0])
    (countLoop .t3 [.store .b .t5 .t0 0, .addi .t0 .t0 1])

end VG.Impl.Rsa.RISCV64.Keys
