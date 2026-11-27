module

public import VerifiedGarbage.Impl.Aes.AArch64.Sbox

/-!
# Bytes and bit slices on AArch64

As on x86-64 (`Impl/Aes/X86_64/Linear.lean`): exchanges of bits within a
word or between two words, the transpose of the eight 8×8 bit matrices that
the registers `q 0 … q 7` hold, one byte each (`ortho`, its own inverse: bit
`j` of byte `p` of `q k` becomes bit `k` of byte `p` of `q j`), and
permutations of those registers' bytes (`zip1`, `zip2`, `swap8`). The masks
are in registers (`m`), and a rotation is part of the instruction that XORs
its result: an exchange is four instructions.

The bits of a word are numbered by their index in binary; exchanging two
index bits is an exchange at the distance of their place values, between the
positions where the lower one is 1 and the higher 0 and those where they are
0 and 1. An index bit within a word is exchanged with a bit of the word's
number by the same exchange between two words, so a transpose of an 8×8
matrix, which exchanges three index bits of the column with three of the
row's, is three passes of exchanges over the four pairs of words.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- Halfword `k` of a constant. -/
def half (v : BitVec 64) (k : Nat) : BitVec 16 := v.extractLsb' (16 * k) 16

/-- `d := v`. -/
def imm (d : Reg) (v : BitVec 64) : List Instr :=
  .movz .x d (half v 0) 0 ::
    (([1, 2, 3] : List Nat).filter (half v · != 0)).map fun k => .movk .x d (half v k) k

/-- `d := a ⊕ (b ror n)`. -/
def eorRor (d a b : Reg) (n : Nat) : Instr := .logicRor .eor .x d a b n

/-- The registers of the masks. -/
def m : Nat → Reg
  | 1 => .x14 | 2 => .x15 | 3 => .x16 | 4 => .x17 | 5 => .x19 | _ => .x20

/-- Constants into the masks' registers. -/
def setMasks (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => imm (m k) v

/-- Exchange the bits of `r` at the positions of the mask in `mk` with
those `n` positions above them. -/
def swapIn (r t mk : Reg) (n : Nat) : List Instr :=
  [eorRor t r r n, andR t t mk, eorR r r t, eorRor r r t (64 - n)]

/-- Exchange the bits of `lo` `n` positions above those of the mask in `mk`
with the bits of `hi` at those positions. -/
def swapMove (lo hi t mk : Reg) (n : Nat) : List Instr :=
  [eorRor t hi lo n, andR t t mk, eorR hi hi t, eorRor lo lo t (64 - n)]

/-- The masks: the bytes' orders' (1–3) and `ortho`'s (4–6). -/
def bsMasks : List (Nat × BitVec 64) :=
  [(1, 0x00000000FFFF0000), (2, 0x0000FF000000FF00), (3, 0x00FF00FF00FF00FF),
   (4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]

/-- Bytes 2, 3 and 4, 5 of each word exchanged. -/
def zip1 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) t0 (m 1) 16

/-- Bytes 1 and 2, and 5 and 6, of each word exchanged. -/
def zip2 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) t0 (m 2) 8

/-- The odd bytes of `q k` and the even bytes of `q (k + 4)` exchanged. -/
def swap8 : List Instr := (List.range 4).flatMap fun k => swapMove (q k) (q (k + 4)) t0 (m 3) 8

/-- Exchange index bit `i` of the bits with bit `i` of the register's number. -/
def exchange (i mk : Nat) : List Instr :=
  ((List.range 8).filter fun k => k / 2 ^ i % 2 == 0).flatMap fun k =>
    swapMove (q k) (q (k + 2 ^ i)) t0 (m mk) (2 ^ i)

/-- The transpose. -/
def ortho : List Instr := exchange 2 6 ++ exchange 1 5 ++ exchange 0 4

end VG.Impl.Aes.AArch64
