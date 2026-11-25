module

public import VerifiedGarbage.Impl.Aes.RISCV64.Sbox
public import VerifiedGarbage.Impl.Words64.RISCV64

/-!
# Bytes and bit slices on RISC-V

Exchanges of bits within a word or between two words, and what they make:
the transpose of the eight 8×8 bit matrices that the registers `q 0 … q 7`
hold, one byte each (`ortho`, its own inverse: bit `j` of byte `p` of `q k`
becomes bit `k` of byte `p` of `q j`), and permutations of the bytes of
those registers (`zip1`, `zip2`, `swap8`). The masks (`bsMasks`) are kept in
slots and loaded into the registers `m k` (`loadMasks`); `t0` is the only
other temporary.

A bit's position in the eight words has nine index bits, six of them within
the word. Exchanging an index bit of the word's number with one within the
word is an exchange of bits between the pairs of words that differ in the
former, at the distance of the latter's place value: six three-operand
instructions a pair (`swapMove`).
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64

/-- The masks' registers. -/
def m : Nat → Reg
  | 1 => .t3 | 2 => .t4 | 3 => .t5 | 4 => .t6 | 5 => .a6 | _ => .s8

/-- One more temporary. -/
def u7 : Reg := .a7

/-- The rotations' temporary. -/
def rt : Reg := .t4

/-- `d := n ⋙ k`, through `rt` (`RV64I` has no rotate; `n` is not `rt`). -/
def rorI (d n : Reg) (k : Nat) : List Instr :=
  [shrI rt n k, shlI d n (64 - k), xorR d d rt]

/-- Constants into slots from `base` (mask `k` in slot `base + k - 1`),
through `t0` and `t1`. -/
def storeMasks (base : Nat) (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun p => Words64.RISCV64.movImm64 t0 t1 p.2 ++ [stS (base + p.1 - 1) t0]

/-- Masks from their slots to their registers. -/
def loadMasks (base : Nat) (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.map fun p => ldS (m p.1) (base + p.1 - 1)

/-- Exchange the bits of `r` at the positions of the mask `k` with those
`n` positions above them. -/
def swapIn (r t k : Reg) (n : Nat) : List Instr :=
  [shrI t r n, xorR t t r, andR t t k, xorR r r t, shlI t t n, xorR r r t]

/-- Exchange the bits of `lo` `n` positions above those of the mask `k` with
the bits of `hi` at those positions. -/
def swapMove (lo hi t k : Reg) (n : Nat) : List Instr :=
  [shrI t lo n, xorR t t hi, andR t t k, xorR hi hi t, shlI t t n, xorR lo lo t]

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

/-- Exchange bit `b` of the register's number with index bit `i` within the
word (place value `2 ^ i`), through `t`, with the mask in `k`. -/
def exchange (b i : Nat) (t k : Reg) : List Instr :=
  ((List.range 8).filter fun j => j / 2 ^ b % 2 == 0).flatMap fun j =>
    swapMove (q j) (q (j + 2 ^ b)) t k (2 ^ i)

/-- The transpose. -/
def ortho : List Instr :=
  exchange 2 2 t0 (m 6) ++ exchange 1 1 t0 (m 5) ++ exchange 0 0 t0 (m 4)

end VG.Impl.Aes.RISCV64
