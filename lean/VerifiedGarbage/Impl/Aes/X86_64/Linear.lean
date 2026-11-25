module

public import VerifiedGarbage.Impl.Aes.X86_64.Sbox

/-!
# Bytes and bit slices on x86-64

Exchanges of bits within a word or between two words, and what they make:
the transpose of the eight 8×8 bit matrices that the registers `q 0 … q 7`
hold, one byte each (`ortho`, its own inverse: bit `j` of byte `p` of `q k`
becomes bit `k` of byte `p` of `q j`), and permutations of the bytes of
those registers (`zip1`, `zip2`, `swap8`). The masks (`bsMasks`) are in
slots of the scratch buffer; `t0` is the only temporary.

The bits of a word are numbered by their index in binary; exchanging two
index bits is an exchange at the distance of their place values, between the
positions where the lower one is 1 and the higher 0 and those where they are
0 and 1. An index bit within a word is exchanged with a bit of the word's
number by the same exchange between two words, so a transpose of an 8×8
matrix, which exchanges three index bits of the column with three of the
row's, is three passes of exchanges over the four pairs of words.
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64

open VG.X86_64

/-- The memory operand `d` bytes from `b`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := (d : Int) }

def imm (d : Reg) (v : BitVec 64) : Instr := .movImm64 d v
def rorI (d : Reg) (n : Nat) : Instr := .shift .ror d n
def shrI (d : Reg) (n : Nat) : Instr := .shift .shr d n
def shlI (d : Reg) (n : Nat) : Instr := .shift .shl d n

/-- Constants into slots, through `t0`. -/
def setMasks (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => [imm t0 v, st k t0]

/-- Exchange the bits of `r` at the positions of the mask in slot `m` with
those `n` positions above them. -/
def swapIn (r t : Reg) (m n : Nat) : List Instr :=
  [movR t r, shrI t n, xorR t r, andS t m, xorR r t, shlI t n, xorR r t]

/-- Exchange the bits of `lo` `n` positions above those of the mask in slot
`m` with the bits of `hi` at those positions. -/
def swapMove (lo hi t : Reg) (m n : Nat) : List Instr :=
  [movR t lo, shrI t n, xorR t hi, andS t m, xorR hi t, shlI t n, xorR lo t]

/-- The masks, by slot: the bytes' orders' (1–3) and `ortho`'s (4–6). -/
def bsMasks : List (Nat × BitVec 64) :=
  [(1, 0x00000000FFFF0000), (2, 0x0000FF000000FF00), (3, 0x00FF00FF00FF00FF),
   (4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]

/-- Bytes 2, 3 and 4, 5 of each word exchanged. -/
def zip1 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) t0 1 16

/-- Bytes 1 and 2, and 5 and 6, of each word exchanged. -/
def zip2 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) t0 2 8

/-- The odd bytes of `q k` and the even bytes of `q (k + 4)` exchanged. -/
def swap8 : List Instr := (List.range 4).flatMap fun k => swapMove (q k) (q (k + 4)) t0 3 8

/-- Exchange index bit `i` of the bits with bit `i` of the register's number. -/
def exchange (i m : Nat) : List Instr :=
  ((List.range 8).filter fun k => k / 2 ^ i % 2 == 0).flatMap fun k =>
    swapMove (q k) (q (k + 2 ^ i)) t0 m (2 ^ i)

/-- The transpose. -/
def ortho : List Instr := exchange 2 6 ++ exchange 1 5 ++ exchange 0 4

end VG.Impl.Aes.X86_64
