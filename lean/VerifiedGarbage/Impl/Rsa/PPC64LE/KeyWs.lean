module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# The working space of the RSA key operations on PPC64LE

The key operations (`vg_rsa_crt_values` and those after it) keep their
numbers in the caller's working space, laid out as on ARMv7
(`Proof/Rsa/KeyWorkspace.lean`): a header of `hdr` bytes, then arrays of
`w + 2` digits of 32 bits, array `j` at byte `hdr + j S` with the stride
`S = 4 (w + 2)`. Numbers are `w` digits, least significant first; the
digits after them are the division's extra digit and the halving's incoming
digit. A sum or difference of two digits is computed in 64 bits, its carry
or borrow in the upper half, without the carry bit.

The base `B` is in `r31`, the stride in `r30` and `w` in `r29`, which the
operations here leave alone: they compute every address from them (`ptr`),
so their addresses and branches depend only on `w` and `B`. The word loops
use `r5`–`r8` (pointers and the count), `r9` (the borrow, the carry or a
mask) and `r0`, `r3` (temporaries), all volatile:

* `sub3 o a b`: `[o] := [a] - [b]` modulo `2^(32 w)`, the borrow in `r9`.
* `sel o a b sl`: `[o] := [b]` if the slot `sl` holds 1, `[a]` if it holds 0.
* `copy o a`: `[o] := [a]`.
* `half j`: `[j] := ([j] + r9 · 2^(32 w)) / 2`, for `r9` 0 or 1.
* `eqS d a b`: the slot `d` := 1 if `[a] = [b]`, 0 otherwise.
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.Keys

open VG.PPC64LE

/-- Right-nested sequencing. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- The header's size in bytes: the arrays start there. -/
def hdr : Nat := 160

/-- Slots of the shared routines (32 bits each). -/
def sOdd : Nat := 124
def sB : Nat := 128
def sC : Nat := 132

/-- `do body; cnt -= 1 while cnt ≠ 0`, for `cnt` at least 1. -/
def countLoop (cnt : Reg) (body : List Instr) : Prog isa :=
  .loop (.block (body ++ ([.subi cnt cnt 1] : List Instr))) (.nonzero .d cnt)

/-- `r` := the address of array `j`, `B + hdr + j S`. -/
def ptr (r : Reg) (j : Nat) : List Instr :=
  [.li r j, .mul r r .r30, .add r r .r31, .addi r r hdr]

/-- `even` if `w` (`r29`) is even, else `odd`: for an even `w` the
operations work on `w / 2` words of 64 bits, for an odd one on digits. -/
def evenW (even odd : Prog isa) : Prog isa :=
  .seq (.block [.li .r0 1, .logic .and .r0 .r29 .r0]) (.ite (.zero .d .r0) even odd)

/-- `r30 := 4 (r29 + 2)`, the stride. -/
def stride : List Instr := [.addi .r30 .r29 2, .lsl .r30 .r30 2]

/-- One digit of `[a] - [b]`, the borrow in `r9`, to `[o]`. -/
def subBody : List Instr :=
  [.load .w .r0 .r6 0, .load .w .r3 .r7 0, .sub .r0 .r0 .r3, .sub .r0 .r0 .r9,
    .store .w .r0 .r5 0, .lsr .d .r9 .r0 63, .addi .r5 .r5 4, .addi .r6 .r6 4,
    .addi .r7 .r7 4]

/-- One word of `[a] - [b]`, the borrow in the carry bit (clear for a borrow). -/
def subWBody : List Instr :=
  [.load .d .r0 .r6 0, .load .d .r3 .r7 0, .sube .r0 .r0 .r3, .store .d .r0 .r5 0,
    .addi .r5 .r5 8, .addi .r6 .r6 8, .addi .r7 .r7 8]

/-- `[o] := [a] - [b]`, the borrow out in `r9`: `w / 2` words with the carry
bit, set first (`0 - 0` does not borrow). -/
def sub3 (o a b : Nat) : Prog isa :=
  .seq (.block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b))
    (evenW (.seq (.block [.lsr .d .r8 .r29 1, .subc .r0 .r8 .r8])
        (.seq (countLoop .r8 subWBody) (.block [.li .r9 0, .adde .r9 .r9 .r9, .li .r0 1, .logic .xor .r9 .r9 .r0])))
      (.seq (.block [.addi .r8 .r29 0, .li .r9 0]) (countLoop .r8 subBody)))

/-- One digit of `mask ? [b] : [a]`, the mask in `r9`, to `[o]`. -/
def selBody : List Instr :=
  [.load .w .r0 .r6 0, .load .w .r3 .r7 0, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
    .logic .xor .r3 .r3 .r0, .store .w .r3 .r5 0, .addi .r5 .r5 4, .addi .r6 .r6 4,
    .addi .r7 .r7 4]

/-- One word of `mask ? [b] : [a]`, the mask in `r9`, to `[o]`. -/
def selWBody : List Instr :=
  [.load .d .r0 .r6 0, .load .d .r3 .r7 0, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
    .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0, .addi .r5 .r5 8, .addi .r6 .r6 8,
    .addi .r7 .r7 8]

/-- `[o] := [b]` if the slot `sl` holds 1, else `[a]`. -/
def sel (o a b sl : Nat) : Prog isa :=
  .seq (.block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ [.load .w .r9 .r31 sl, .li .r0 0, .sub .r9 .r0 .r9]))
    (evenW (.seq (.block [.lsr .d .r8 .r29 1]) (countLoop .r8 selWBody))
      (.seq (.block [.addi .r8 .r29 0]) (countLoop .r8 selBody)))

/-- One digit of `[a]` to `[o]`. -/
def copyBody : List Instr :=
  [.load .w .r0 .r6 0, .store .w .r0 .r5 0, .addi .r5 .r5 4, .addi .r6 .r6 4]

/-- One word of `[a]` to `[o]`. -/
def copyWBody : List Instr :=
  [.load .d .r0 .r6 0, .store .d .r0 .r5 0, .addi .r5 .r5 8, .addi .r6 .r6 8]

/-- `[o] := [a]`. -/
def copy (o a : Nat) : Prog isa :=
  .seq (.block (ptr .r5 o ++ ptr .r6 a))
    (evenW (.seq (.block [.lsr .d .r8 .r29 1]) (countLoop .r8 copyWBody))
      (.seq (.block [.addi .r8 .r29 0]) (countLoop .r8 copyBody)))

/-- One digit of the halving: the digit at `r5` := its upper 31 bits and the
low bit of the next digit. -/
def halfBody : List Instr :=
  [.load .w .r0 .r5 0, .load .w .r3 .r5 4, .lsl .r3 .r3 31, .lsr .d .r0 .r0 1,
    .logic .or .r0 .r0 .r3, .store .w .r0 .r5 0, .addi .r5 .r5 4]

/-- One word of the halving: the word at `r5` := its upper 63 bits and the
low bit of the next digit. -/
def halfWBody : List Instr :=
  [.load .d .r0 .r5 0, .load .w .r3 .r5 8, .lsl .r3 .r3 63, .lsr .d .r0 .r0 1,
    .logic .or .r0 .r0 .r3, .store .d .r0 .r5 0, .addi .r5 .r5 8]

/-- `[j] := ([j] + r9 · 2^(32 w)) / 2`: `r9` stored as digit `w`, then the shift. -/
def half (j : Nat) : Prog isa :=
  .seq (.block (ptr .r5 j ++ [.lsl .r6 .r29 2, .add .r6 .r5 .r6, .store .w .r9 .r6 0]))
    (evenW (.seq (.block [.lsr .d .r8 .r29 1]) (countLoop .r8 halfWBody))
      (.seq (.block [.addi .r8 .r29 0]) (countLoop .r8 halfBody)))

/-- The slot `sl` := the low bit of `[j]`. -/
def bitOf (sl j : Nat) : List Instr :=
  ptr .r5 j ++ [.load .w .r0 .r5 0, .li .r3 1, .logic .and .r0 .r0 .r3, .store .w .r0 .r31 sl]

/-- The borrow (`r9`) to the slot `sl`. -/
def stBorrow (sl : Nat) : List Instr := [.store .w .r9 .r31 sl]

/-- The slot `d` := the slots `a` and `b` and'ed. -/
def andS (d a b : Nat) : List Instr :=
  [.load .w .r0 .r31 a, .load .w .r3 .r31 b, .logic .and .r0 .r0 .r3, .store .w .r0 .r31 d]

/-- The low digit of `[j]` := 1. -/
def setOne (j : Nat) : List Instr := ptr .r5 j ++ [.li .r0 1, .store .w .r0 .r5 0]

/-- The low bit of `[j]` set. -/
def orOne (j : Nat) : List Instr :=
  ptr .r5 j ++ [.load .w .r0 .r5 0, .li .r3 1, .logic .or .r0 .r0 .r3, .store .w .r0 .r5 0]

/-- The low bit of `[j]` cleared: the low digit shifted right by one and back. -/
def clrLow (j : Nat) : List Instr :=
  ptr .r5 j ++ [.load .w .r0 .r5 0, .lsr .d .r0 .r0 1, .lsl .r0 .r0 1, .store .w .r0 .r5 0]

/-- One digit of the comparison: `r9 |= [a] ^ [b]`. -/
def eqBody : List Instr :=
  [.load .w .r0 .r6 0, .load .w .r3 .r7 0, .logic .xor .r0 .r0 .r3, .logic .or .r9 .r9 .r0,
    .addi .r6 .r6 4, .addi .r7 .r7 4]

/-- One word of the comparison: `r9 |= [a] ^ [b]`. -/
def eqWBody : List Instr :=
  [.load .d .r0 .r6 0, .load .d .r3 .r7 0, .logic .xor .r0 .r0 .r3, .logic .or .r9 .r9 .r0,
    .addi .r6 .r6 8, .addi .r7 .r7 8]

/-- The slot `d` := 1 if `[a] = [b]`, else 0: the digits' (or words')
differences or'ed into `r9`, which is 0 exactly when they are equal, then
`1 - (0 - r9) >> 63` (`1 - (r9 | (0 - r9)) >> 63` for words). -/
def eqS (d a b : Nat) : Prog isa :=
  .seq (.block (ptr .r6 a ++ ptr .r7 b ++ [.li .r9 0]))
    (evenW
      (.seq (.block [.lsr .d .r8 .r29 1]) (.seq (countLoop .r8 eqWBody)
        (.block [.li .r0 0, .sub .r0 .r0 .r9, .logic .or .r0 .r0 .r9, .lsr .d .r0 .r0 63, .li .r3 1,
          .logic .xor .r0 .r0 .r3, .store .w .r0 .r31 d])))
      (.seq (.block [.addi .r8 .r29 0]) (.seq (countLoop .r8 eqBody)
        (.block [.li .r0 0, .sub .r0 .r0 .r9, .lsr .d .r0 .r0 63, .li .r3 1,
          .logic .xor .r0 .r0 .r3, .store .w .r0 .r31 d]))))

/-- The `c` digits from array 0 on (at `B + hdr`) := 0. -/
def zeroArrays (c : Reg) : Prog isa :=
  .seq (.block [.addi .r5 .r31 hdr, .li .r0 0]) (countLoop c [.store .w .r0 .r5 0, .addi .r5 .r5 4])

end VG.Impl.Rsa.PPC64LE.Keys
