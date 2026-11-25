module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Sbox

/-!
# Bytes and bit slices on PPC64LE

As on AArch64 (`Impl/Aes/AArch64/Linear.lean`): the transpose of the eight
8×8 bit matrices that the registers `q 0 … q 7` hold, one byte each
(`ortho`, its own inverse), and permutations of those registers' bytes
(`zip1`, `zip2`, `swap8`), as exchanges of index bits, with the masks in
registers (`m`).
-/

@[expose] public section

namespace VG.Impl.Aes.PPC64LE

open VG.PPC64LE

/-- `d := v`. -/
def imm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- The registers of the masks. -/
def m : Nat → Reg
  | 1 => .r26 | 2 => .r27 | 3 => .r28 | 4 => .r29 | 5 => .r30 | _ => .r31

/-- Constants into the masks' registers. -/
def setMasks (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => imm64 (m k) v

/-- Exchange the bits of `r` at the positions of the mask in `mk` with
those `n` positions above them. -/
def swapIn (r t mk : Reg) (n : Nat) : List Instr :=
  [rorI t r n, xorR t t r, andR t t mk, xorR r r t, rorI t t (64 - n), xorR r r t]

/-- Exchange the bits of `lo` `n` positions above those of the mask in `mk`
with the bits of `hi` at those positions. -/
def swapMove (lo hi t mk : Reg) (n : Nat) : List Instr :=
  [rorI t lo n, xorR t t hi, andR t t mk, xorR hi hi t, rorI t t (64 - n), xorR lo lo t]

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

end VG.Impl.Aes.PPC64LE
