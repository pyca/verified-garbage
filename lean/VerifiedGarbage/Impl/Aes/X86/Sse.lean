module

public import VerifiedGarbage.Impl.Aes.X86.Ctr32

/-!
# Bitsliced AES on x86 (32-bit), eight blocks at a time in SSE2 registers

Slice `j`, 128 bits, holds bit `j` of every byte of eight blocks: the byte of
row `r` and column `c` of block `k` is at bit `k + 8 (c + 4 r)`. So a row is a
doubleword and a column is a byte of it: the next row is a shuffle of
doublewords, all rows' columns are rotated by one by rotating doublewords by
eight bits, and by two by shuffling words.

**ShiftRows is not done.** A round that leaves every byte where it is leaves
the byte of row `r` and column `c` at column `c + r` (form 1 of the state,
where form 0 is the plain one), which the next layer allows for: MixColumns
of form 1 takes the next row's byte one column further, and the round key is
stored in form 1. The next round does ShiftRows twice, which moves only the
odd rows, by two columns, a word of their doublewords, and gives form 0
again. The rounds are even in number, and go in pairs. The inverse cipher's
pairs start with ShiftRows twice, which from form 0 gives InvShiftRows in
form 1, and end with none.

**The S-box's constant is in the round keys.** `{63}` in every byte goes
through ShiftRows and MixColumns unchanged (`2 + 3 + 1 + 1 = 1`), so the
round keys but the first have it added, and `subBytes` computes the S-box
without it; likewise `invSubBytes` takes its input with it added.

**The first and the last round key** are added to the blocks' bytes, so that
only those between are made into slices: 128 bytes each, as a byte of a slice
is eight blocks' bits.

Eight registers hold no more than the eight slices, so the S-boxes and the
linear layers are written out in an order, and with an allocation of
registers and slots, found by a search for few instructions. A state between
rounds has slices 0–3 in `xmm0`–`xmm3` and slices 4–7 in their slots; after
an S-box, slices are where `subOut` and `invSubOut` say.

The scratch buffer (at `edi`), in slots of 16 bytes: the eight blocks of a
batch, and then its slices and what the layers spill (0–17); the last round
key with `{63}` added (18); the caller's registers (19); the counter block
(20); the round keys (24–127).
-/

@[expose] public section

namespace VG.Impl.Aes.X86.Sse

open VG.X86 VG.Impl.Aes.X86

/-! ## Short forms -/

/-- Slot `k` of the scratch buffer. -/
def slot (k : Nat) : MemOp := at_ sb (16 * k)

/-- The pointer to the round key. -/
def kp : Reg := .eax

def mv (d s : XReg) : Instr := .xop (.bin .movdqa d s)
def px (d s : XReg) : Instr := .xop (.bin .pxor d s)
def an (d s : XReg) : Instr := .xop (.bin .pand d s)
def lwd (d s : XReg) : Instr := .xop (.bin .punpcklwd d s)
def hwd (d s : XReg) : Instr := .xop (.bin .punpckhwd d s)
def ldq (d s : XReg) : Instr := .xop (.bin .punpckldq d s)
def hdq (d s : XReg) : Instr := .xop (.bin .punpckhdq d s)
def lqdq (d s : XReg) : Instr := .xop (.bin .punpcklqdq d s)
def hqdq (d s : XReg) : Instr := .xop (.bin .punpckhqdq d s)
def shd (d s : XReg) (o : BitVec 8) : Instr := .xop (.pshufd d s o)
def slw (d s : XReg) (o : BitVec 8) : Instr := .xop (.pshuflw d s o)
def shw (d s : XReg) (o : BitVec 8) : Instr := .xop (.pshufhw d s o)
def srd (d : XReg) (n : Nat) : Instr := .xop (.shift .psrld d (BitVec.ofNat 8 n))
def sld (d : XReg) (n : Nat) : Instr := .xop (.shift .pslld d (BitVec.ofNat 8 n))
def srq (d : XReg) (n : Nat) : Instr := .xop (.shift .psrlq d (BitVec.ofNat 8 n))
def slq (d : XReg) (n : Nat) : Instr := .xop (.shift .psllq d (BitVec.ofNat 8 n))

/-- Slot `k`, loaded and stored, and word `k` (of 16 bytes) at `kp`. -/
def ld (d : XReg) (k : Nat) : Instr := .movdquLoad d (slot k)
def sv (k : Nat) (s : XReg) : Instr := .movdquStore (slot k) s
def lk (d : XReg) (k : Nat) : Instr := .movdquLoad d (at_ kp (16 * k))

/-! ## The rounds -/

/-- Where a slice is. -/
inductive Loc
  | x (r : XReg)
  | m (k : Nat)
  deriving DecidableEq

/-- Where slice `j` is between rounds. -/
def mid : Nat → Loc
  | 0 => .x .xmm0 | 1 => .x .xmm1 | 2 => .x .xmm2 | 3 => .x .xmm3 | j => .m j

/-- The S-box without its constant, from `mid`. -/
def subBytes : List Instr := [
  ld .xmm4 5, px .xmm2 .xmm4, mv .xmm5 .xmm2, px .xmm5 .xmm1, ld .xmm6 6, px .xmm6 .xmm5, px .xmm3 .xmm6,
  ld .xmm7 7, px .xmm3 .xmm7, sv 0 .xmm6, mv .xmm6 .xmm3, px .xmm6 .xmm2, px .xmm0 .xmm5, px .xmm7 .xmm0,
  sv 1 .xmm7, mv .xmm7 .xmm6, px .xmm7 .xmm0, sv 2 .xmm0, ld .xmm0 4, px .xmm0 .xmm6, sv 3 .xmm6, ld .xmm6 4,
  px .xmm6 .xmm3, px .xmm1 .xmm0, sv 5 .xmm6, ld .xmm6 4, px .xmm6 .xmm7, px .xmm4 .xmm7, sv 4 .xmm0, ld .xmm0 0,
  px .xmm0 .xmm7, sv 8 .xmm0, ld .xmm0 7, px .xmm0 .xmm4, sv 9 .xmm4, mv .xmm4 .xmm6, an .xmm4 .xmm7, sv 10 .xmm7,
  ld .xmm7 8, px .xmm7 .xmm1, sv 11 .xmm7, ld .xmm7 1, an .xmm7 .xmm1, px .xmm3 .xmm6, sv 12 .xmm1, ld .xmm1 4,
  an .xmm1 .xmm3, sv 13 .xmm3, mv .xmm3 .xmm6, px .xmm3 .xmm0, sv 14 .xmm6, ld .xmm6 8, an .xmm6 .xmm3,
  px .xmm6 .xmm1, sv 15 .xmm3, ld .xmm3 7, an .xmm3 .xmm5, px .xmm7 .xmm6, px .xmm7 .xmm4, px .xmm7 .xmm2,
  ld .xmm2 0, an .xmm2 .xmm0, px .xmm4 .xmm3, ld .xmm3 6, px .xmm3 .xmm0, px .xmm1 .xmm2, px .xmm4 .xmm1,
  px .xmm3 .xmm4, ld .xmm2 9, ld .xmm4 4, px .xmm4 .xmm2, sv 16 .xmm0, ld .xmm0 11, an .xmm0 .xmm4, px .xmm0 .xmm6,
  ld .xmm6 5, sv 17 .xmm4, ld .xmm4 2, an .xmm4 .xmm6, px .xmm1 .xmm4, ld .xmm6 6, an .xmm6 .xmm2, px .xmm1 .xmm6,
  px .xmm0 .xmm4, mv .xmm4 .xmm3, an .xmm4 .xmm7, ld .xmm6 3, px .xmm0 .xmm6, px .xmm2 .xmm5, px .xmm1 .xmm2,
  mv .xmm2 .xmm1, px .xmm2 .xmm4, px .xmm4 .xmm0, mv .xmm6 .xmm7, px .xmm6 .xmm0, an .xmm2 .xmm6, px .xmm2 .xmm0,
  px .xmm3 .xmm1, px .xmm7 .xmm2, mv .xmm6 .xmm4, px .xmm6 .xmm2, an .xmm6 .xmm0, px .xmm7 .xmm6, an .xmm5 .xmm2,
  px .xmm6 .xmm4, an .xmm4 .xmm3, px .xmm4 .xmm1, ld .xmm0 1, an .xmm0 .xmm4, an .xmm6 .xmm4, px .xmm6 .xmm3,
  mv .xmm1 .xmm4, px .xmm1 .xmm2, ld .xmm3 0, an .xmm3 .xmm7, sv 0 .xmm2, ld .xmm2 8, an .xmm2 .xmm6, sv 1 .xmm0,
  ld .xmm0 12, an .xmm0 .xmm4, px .xmm4 .xmm6, px .xmm3 .xmm5, px .xmm0 .xmm2, sv 3 .xmm5, ld .xmm5 15,
  an .xmm5 .xmm6, px .xmm0 .xmm3, px .xmm6 .xmm7, sv 8 .xmm3, ld .xmm3 11, an .xmm3 .xmm4, px .xmm3 .xmm2,
  ld .xmm2 5, an .xmm2 .xmm1, px .xmm2 .xmm3, sv 5 .xmm2, ld .xmm2 10, an .xmm2 .xmm6, sv 10 .xmm2, ld .xmm2 2,
  an .xmm2 .xmm1, px .xmm1 .xmm6, sv 2 .xmm3, ld .xmm3 17, an .xmm4 .xmm3, ld .xmm3 14, an .xmm6 .xmm3, ld .xmm3 4,
  an .xmm3 .xmm1, px .xmm3 .xmm5, px .xmm2 .xmm4, px .xmm2 .xmm3, px .xmm2 .xmm0, px .xmm3 .xmm6, ld .xmm6 1,
  px .xmm6 .xmm2, sv 11 .xmm2, ld .xmm2 16, an .xmm2 .xmm7, px .xmm6 .xmm2, ld .xmm2 0, px .xmm7 .xmm2,
  px .xmm6 .xmm5, ld .xmm5 7, an .xmm2 .xmm5, px .xmm6 .xmm2, ld .xmm5 1, px .xmm5 .xmm3, px .xmm2 .xmm4,
  px .xmm3 .xmm2, ld .xmm2 9, an .xmm2 .xmm7, px .xmm3 .xmm2, ld .xmm2 6, an .xmm7 .xmm2, ld .xmm2 13,
  an .xmm1 .xmm2, ld .xmm2 2, px .xmm2 .xmm1, ld .xmm4 3, px .xmm2 .xmm4, px .xmm1 .xmm5, px .xmm7 .xmm2,
  ld .xmm2 10, px .xmm7 .xmm2, ld .xmm4 8, px .xmm4 .xmm1, px .xmm1 .xmm3, px .xmm2 .xmm4, px .xmm0 .xmm5,
  ld .xmm4 5, px .xmm1 .xmm4]

/-- Where `subBytes` leaves slice `j`. -/
def subOut : Nat → Loc
  | 0 => .m 11 | 1 => .x .xmm5 | 2 => .x .xmm3 | 3 => .x .xmm7 | 4 => .x .xmm6 | 5 => .x .xmm0 | 6 => .x .xmm1
  | _ => .x .xmm2

/-- The inverse S-box of an input with `{63}` added, from `mid`. -/
def invSubBytes : List Instr := [
  ld .xmm4 4, ld .xmm5 5, px .xmm5 .xmm4, px .xmm1 .xmm5, ld .xmm6 6, ld .xmm7 7, px .xmm7 .xmm6, px .xmm6 .xmm1,
  px .xmm4 .xmm2, sv 0 .xmm5, mv .xmm5 .xmm4, px .xmm5 .xmm0, px .xmm0 .xmm7, px .xmm7 .xmm5, sv 1 .xmm4,
  ld .xmm4 5, px .xmm4 .xmm6, sv 2 .xmm5, ld .xmm5 4, px .xmm5 .xmm0, px .xmm3 .xmm1, sv 3 .xmm7, mv .xmm7 .xmm3,
  an .xmm7 .xmm6, sv 4 .xmm4, mv .xmm4 .xmm6, px .xmm4 .xmm0, sv 5 .xmm6, ld .xmm6 4, an .xmm6 .xmm0, sv 6 .xmm0,
  mv .xmm0 .xmm3, px .xmm0 .xmm5, sv 8 .xmm5, mv .xmm5 .xmm1, px .xmm5 .xmm2, sv 9 .xmm0, ld .xmm0 4,
  px .xmm0 .xmm3, sv 10 .xmm3, mv .xmm3 .xmm0, an .xmm3 .xmm4, px .xmm6 .xmm7, sv 11 .xmm4, ld .xmm4 7,
  px .xmm4 .xmm0, px .xmm7 .xmm3, ld .xmm3 7, px .xmm3 .xmm5, sv 7 .xmm0, ld .xmm0 3, px .xmm0 .xmm4,
  px .xmm1 .xmm0, sv 12 .xmm1, mv .xmm1 .xmm3, an .xmm1 .xmm0, sv 13 .xmm0, ld .xmm0 9, px .xmm0 .xmm3, sv 14 .xmm3,
  ld .xmm3 3, an .xmm3 .xmm0, sv 15 .xmm0, ld .xmm0 9, an .xmm0 .xmm4, px .xmm0 .xmm7, px .xmm0 .xmm3,
  px .xmm3 .xmm6, px .xmm3 .xmm1, px .xmm0 .xmm5, px .xmm5 .xmm4, ld .xmm1 5, px .xmm1 .xmm4, sv 16 .xmm4,
  ld .xmm4 1, sv 17 .xmm5, ld .xmm5 12, an .xmm5 .xmm4, px .xmm2 .xmm3, px .xmm7 .xmm5, px .xmm4 .xmm1, ld .xmm3 17,
  an .xmm3 .xmm4, px .xmm3 .xmm6, mv .xmm6 .xmm2, px .xmm6 .xmm0, px .xmm3 .xmm5, ld .xmm5 2, px .xmm3 .xmm5,
  mv .xmm5 .xmm3, an .xmm5 .xmm2, sv 2 .xmm4, ld .xmm4 8, an .xmm4 .xmm1, px .xmm7 .xmm4, ld .xmm4 0,
  px .xmm7 .xmm4, mv .xmm4 .xmm7, px .xmm4 .xmm5, an .xmm4 .xmm6, px .xmm5 .xmm0, px .xmm4 .xmm0, px .xmm2 .xmm4,
  px .xmm3 .xmm7, mv .xmm6 .xmm5, px .xmm6 .xmm4, an .xmm6 .xmm0, px .xmm2 .xmm6, px .xmm6 .xmm5, an .xmm5 .xmm3,
  px .xmm7 .xmm5, an .xmm1 .xmm2, an .xmm6 .xmm7, ld .xmm0 1, an .xmm0 .xmm4, ld .xmm5 3, an .xmm5 .xmm7,
  px .xmm6 .xmm3, ld .xmm3 9, an .xmm3 .xmm6, px .xmm0 .xmm3, sv 0 .xmm3, mv .xmm3 .xmm5, px .xmm3 .xmm1,
  sv 1 .xmm5, mv .xmm5 .xmm2, px .xmm5 .xmm4, px .xmm0 .xmm3, ld .xmm3 16, an .xmm3 .xmm6, sv 3 .xmm1, ld .xmm1 8,
  an .xmm1 .xmm2, px .xmm2 .xmm6, px .xmm6 .xmm7, px .xmm0 .xmm3, sv 8 .xmm3, ld .xmm3 15, an .xmm3 .xmm7,
  sv 9 .xmm6, ld .xmm6 2, an .xmm6 .xmm5, px .xmm3 .xmm0, sv 2 .xmm6, ld .xmm6 12, an .xmm6 .xmm4, sv 12 .xmm0,
  ld .xmm0 17, an .xmm5 .xmm0, px .xmm7 .xmm4, ld .xmm0 4, an .xmm0 .xmm7, ld .xmm4 6, an .xmm4 .xmm7,
  px .xmm0 .xmm5, px .xmm5 .xmm1, px .xmm1 .xmm3, px .xmm1 .xmm6, px .xmm4 .xmm1, sv 15 .xmm1, ld .xmm1 10,
  an .xmm1 .xmm2, px .xmm0 .xmm1, px .xmm0 .xmm6, px .xmm7 .xmm2, ld .xmm6 7, an .xmm6 .xmm7, px .xmm1 .xmm6,
  ld .xmm6 11, an .xmm7 .xmm6, px .xmm1 .xmm3, ld .xmm3 9, ld .xmm6 14, an .xmm6 .xmm3, px .xmm5 .xmm6,
  px .xmm7 .xmm4, ld .xmm6 13, an .xmm3 .xmm6, ld .xmm6 5, an .xmm2 .xmm6, ld .xmm6 8, px .xmm6 .xmm7,
  px .xmm2 .xmm3, px .xmm6 .xmm3, ld .xmm3 3, px .xmm7 .xmm3, ld .xmm3 1, px .xmm4 .xmm3, ld .xmm3 2,
  px .xmm3 .xmm0, px .xmm3 .xmm7, px .xmm2 .xmm4, ld .xmm4 0, px .xmm4 .xmm5, px .xmm4 .xmm2, px .xmm2 .xmm3,
  ld .xmm7 12, px .xmm5 .xmm7]

/-- Where `invSubBytes` leaves slice `j`. -/
def invSubOut : Nat → Loc
  | 0 => .m 15 | 1 => .x .xmm2 | 2 => .x .xmm5 | 3 => .x .xmm0 | 4 => .x .xmm6 | 5 => .x .xmm1 | 6 => .x .xmm3
  | _ => .x .xmm4

/-- MixColumns in form 1, and the round key, from `subOut` to `mid`:
`b ≔ a ⊕ next(a)`, and the result is `2 b ⊕ next(a) ⊕ row2(b)`. -/
def linA : List Instr := [
  shd .xmm4 .xmm2 0x39, sv 0 .xmm5, mv .xmm5 .xmm4, srd .xmm5 8, sld .xmm4 24, px .xmm4 .xmm5, px .xmm2 .xmm4,
  shd .xmm5 .xmm2 0x4e, slw .xmm5 .xmm5 0xb1, shw .xmm5 .xmm5 0xb1, sv 1 .xmm2, shd .xmm2 .xmm1 0x39,
  px .xmm5 .xmm4, mv .xmm4 .xmm2, srd .xmm4 8, sld .xmm2 24, px .xmm4 .xmm2, px .xmm1 .xmm4, shd .xmm2 .xmm1 0x4e,
  px .xmm1 .xmm5, lk .xmm5 7, px .xmm1 .xmm5, shd .xmm5 .xmm0 0x39, slw .xmm2 .xmm2 0xb1, sv 7 .xmm1,
  mv .xmm1 .xmm5, srd .xmm1 8, shw .xmm2 .xmm2 0xb1, px .xmm2 .xmm4, sld .xmm5 24, shd .xmm4 .xmm6 0x39,
  px .xmm5 .xmm1, mv .xmm1 .xmm4, sld .xmm1 24, srd .xmm4 8, px .xmm0 .xmm5, px .xmm2 .xmm0, px .xmm4 .xmm1,
  shd .xmm0 .xmm0 0x4e, lk .xmm1 6, px .xmm2 .xmm1, shd .xmm1 .xmm3 0x39, px .xmm6 .xmm4, sv 6 .xmm2,
  mv .xmm2 .xmm1, srd .xmm2 8, sld .xmm1 24, px .xmm2 .xmm1, slw .xmm0 .xmm0 0xb1, shd .xmm1 .xmm7 0x39,
  shw .xmm0 .xmm0 0xb1, px .xmm3 .xmm2, px .xmm5 .xmm0, shd .xmm0 .xmm6 0x4e, slw .xmm0 .xmm0 0xb1,
  shw .xmm0 .xmm0 0xb1, px .xmm0 .xmm4, mv .xmm4 .xmm1, sld .xmm4 24, srd .xmm1 8, px .xmm1 .xmm4,
  shd .xmm4 .xmm3 0x4e, px .xmm7 .xmm1, slw .xmm4 .xmm4 0xb1, px .xmm0 .xmm7, shd .xmm7 .xmm7 0x4e,
  slw .xmm7 .xmm7 0xb1, shw .xmm7 .xmm7 0xb1, px .xmm1 .xmm7, px .xmm3 .xmm1, shw .xmm4 .xmm4 0xb1, px .xmm5 .xmm6,
  lk .xmm1 5, px .xmm5 .xmm1, px .xmm2 .xmm4, ld .xmm1 0, shd .xmm4 .xmm1 0x39, mv .xmm6 .xmm4, sld .xmm6 24,
  srd .xmm4 8, px .xmm4 .xmm6, px .xmm1 .xmm4, shd .xmm6 .xmm1 0x4e, ld .xmm7 1, px .xmm0 .xmm7, sv 5 .xmm5,
  lk .xmm5 4, px .xmm0 .xmm5, slw .xmm6 .xmm6 0xb1, px .xmm2 .xmm1, ld .xmm1 11, shd .xmm5 .xmm1 0x39, sv 4 .xmm0,
  mv .xmm0 .xmm5, sld .xmm0 24, srd .xmm5 8, px .xmm0 .xmm5, px .xmm1 .xmm0, px .xmm3 .xmm7, shd .xmm5 .xmm1 0x4e,
  shw .xmm6 .xmm6 0xb1, px .xmm6 .xmm4, px .xmm1 .xmm6, lk .xmm4 2, px .xmm2 .xmm4, slw .xmm5 .xmm5 0xb1,
  shw .xmm5 .xmm5 0xb1, lk .xmm4 3, px .xmm3 .xmm4, px .xmm0 .xmm5, px .xmm1 .xmm7, px .xmm0 .xmm7, lk .xmm4 1,
  px .xmm1 .xmm4, lk .xmm4 0, px .xmm0 .xmm4]

/-- ShiftRows twice, MixColumns in form 0, and the round key, from `subOut` to `mid`. -/
def linB : List Instr := [
  slw .xmm2 .xmm2 0xb4, slw .xmm7 .xmm7 0xb4, shw .xmm2 .xmm2 0xb4, shd .xmm4 .xmm2 0x39, slw .xmm1 .xmm1 0xb4,
  slw .xmm3 .xmm3 0xb4, px .xmm2 .xmm4, shw .xmm1 .xmm1 0xb4, sv 0 .xmm5, shd .xmm5 .xmm2 0x4e,
  slw .xmm0 .xmm0 0xb4, px .xmm4 .xmm5, shd .xmm5 .xmm1 0x39, shw .xmm7 .xmm7 0xb4, px .xmm1 .xmm5, px .xmm4 .xmm1,
  shw .xmm0 .xmm0 0xb4, shd .xmm1 .xmm1 0x4e, px .xmm5 .xmm1, slw .xmm6 .xmm6 0xb4, lk .xmm1 7, px .xmm4 .xmm1,
  shd .xmm1 .xmm0 0x39, px .xmm0 .xmm1, px .xmm5 .xmm0, shd .xmm0 .xmm0 0x4e, shw .xmm6 .xmm6 0xb4, sv 7 .xmm4,
  shd .xmm4 .xmm6 0x39, px .xmm1 .xmm0, px .xmm6 .xmm4, shw .xmm3 .xmm3 0xb4, lk .xmm0 6, px .xmm5 .xmm0,
  ld .xmm0 11, slw .xmm0 .xmm0 0xb4, px .xmm1 .xmm6, shd .xmm6 .xmm6 0x4e, sv 6 .xmm5, shd .xmm5 .xmm7 0x39,
  px .xmm7 .xmm5, px .xmm4 .xmm6, px .xmm4 .xmm7, shd .xmm7 .xmm7 0x4e, px .xmm4 .xmm2, lk .xmm6 5, px .xmm1 .xmm6,
  ld .xmm6 0, slw .xmm6 .xmm6 0xb4, sv 5 .xmm1, shd .xmm1 .xmm3 0x39, px .xmm3 .xmm1, px .xmm7 .xmm5,
  shd .xmm5 .xmm3 0x4e, shw .xmm0 .xmm0 0xb4, shw .xmm6 .xmm6 0xb4, px .xmm3 .xmm7, lk .xmm7 4, px .xmm4 .xmm7,
  shd .xmm7 .xmm6 0x39, px .xmm6 .xmm7, px .xmm3 .xmm2, px .xmm5 .xmm1, shd .xmm1 .xmm6 0x4e, sv 4 .xmm4,
  shd .xmm4 .xmm0 0x39, px .xmm0 .xmm4, px .xmm5 .xmm6, px .xmm1 .xmm7, px .xmm1 .xmm0, shd .xmm0 .xmm0 0x4e,
  px .xmm0 .xmm4, lk .xmm4 3, px .xmm3 .xmm4, px .xmm1 .xmm2, lk .xmm4 1, px .xmm1 .xmm4, px .xmm0 .xmm2,
  lk .xmm2 0, px .xmm0 .xmm2, lk .xmm2 2, px .xmm5 .xmm2, mv .xmm2 .xmm5]

/-- The round key and InvMixColumns in form 1, from `invSubOut` to `mid`:
MixColumns of `a ⊕ 4 (a ⊕ row2(a))`. -/
def invLinA : List Instr := [
  lk .xmm7 5, px .xmm1 .xmm7, lk .xmm7 3, px .xmm0 .xmm7, lk .xmm7 4, px .xmm6 .xmm7, lk .xmm7 2, px .xmm5 .xmm7,
  shd .xmm7 .xmm6 0x4e, sv 0 .xmm2, shd .xmm2 .xmm1 0x4e, sv 1 .xmm5, lk .xmm5 7, px .xmm4 .xmm5,
  slw .xmm2 .xmm2 0xb1, lk .xmm5 6, px .xmm3 .xmm5, slw .xmm7 .xmm7 0xb1, shd .xmm5 .xmm0 0x4e,
  shw .xmm2 .xmm2 0xb1, slw .xmm5 .xmm5 0xb1, shw .xmm7 .xmm7 0xb1, shw .xmm5 .xmm5 0xb1, px .xmm7 .xmm6,
  sv 2 .xmm6, shd .xmm6 .xmm4 0x4e, px .xmm2 .xmm1, px .xmm2 .xmm4, px .xmm5 .xmm0, slw .xmm6 .xmm6 0xb1,
  px .xmm7 .xmm3, sv 3 .xmm0, shd .xmm0 .xmm2 0x39, shw .xmm6 .xmm6 0xb1, px .xmm6 .xmm4, px .xmm1 .xmm5,
  mv .xmm4 .xmm0, sld .xmm4 24, srd .xmm0 8, px .xmm0 .xmm4, px .xmm2 .xmm0, shd .xmm4 .xmm2 0x4e,
  slw .xmm4 .xmm4 0xb1, shw .xmm4 .xmm4 0xb1, shd .xmm5 .xmm3 0x4e, slw .xmm5 .xmm5 0xb1, sv 8 .xmm2,
  shd .xmm2 .xmm7 0x39, px .xmm1 .xmm6, px .xmm0 .xmm4, mv .xmm4 .xmm2, srd .xmm4 8, sld .xmm2 24, px .xmm2 .xmm4,
  px .xmm7 .xmm2, px .xmm0 .xmm7, shd .xmm7 .xmm7 0x4e, shd .xmm4 .xmm1 0x39, sv 7 .xmm0, mv .xmm0 .xmm4,
  srd .xmm0 8, shw .xmm5 .xmm5 0xb1, slw .xmm7 .xmm7 0xb1, sld .xmm4 24, px .xmm4 .xmm0, px .xmm3 .xmm5, lk .xmm0 0,
  ld .xmm5 15, px .xmm5 .xmm0, shw .xmm7 .xmm7 0xb1, shd .xmm0 .xmm5 0x4e, px .xmm2 .xmm7, slw .xmm0 .xmm0 0xb1,
  px .xmm1 .xmm4, shw .xmm0 .xmm0 0xb1, px .xmm2 .xmm1, ld .xmm7 0, sv 6 .xmm2, lk .xmm2 1, px .xmm2 .xmm7,
  px .xmm0 .xmm5, ld .xmm7 1, px .xmm0 .xmm7, shd .xmm1 .xmm1 0x4e, px .xmm5 .xmm3, slw .xmm1 .xmm1 0xb1,
  shw .xmm1 .xmm1 0xb1, sv 0 .xmm5, shd .xmm5 .xmm7 0x4e, slw .xmm5 .xmm5 0xb1, shw .xmm5 .xmm5 0xb1,
  px .xmm1 .xmm4, shd .xmm4 .xmm2 0x4e, px .xmm7 .xmm5, slw .xmm4 .xmm4 0xb1, shw .xmm4 .xmm4 0xb1, px .xmm0 .xmm6,
  px .xmm4 .xmm2, px .xmm6 .xmm3, ld .xmm5 3, px .xmm4 .xmm5, ld .xmm5 2, px .xmm7 .xmm5, px .xmm7 .xmm6,
  px .xmm2 .xmm6, shd .xmm5 .xmm7 0x39, px .xmm4 .xmm3, mv .xmm3 .xmm5, sld .xmm3 24, shd .xmm6 .xmm4 0x39,
  srd .xmm5 8, px .xmm3 .xmm5, px .xmm7 .xmm3, px .xmm1 .xmm7, shd .xmm7 .xmm7 0x4e, shd .xmm5 .xmm0 0x39,
  slw .xmm7 .xmm7 0xb1, sv 5 .xmm1, mv .xmm1 .xmm6, sld .xmm1 24, srd .xmm6 8, px .xmm6 .xmm1, shw .xmm7 .xmm7 0xb1,
  px .xmm4 .xmm6, mv .xmm1 .xmm5, srd .xmm1 8, px .xmm7 .xmm3, shd .xmm3 .xmm4 0x4e, slw .xmm3 .xmm3 0xb1,
  shw .xmm3 .xmm3 0xb1, px .xmm7 .xmm4, shd .xmm4 .xmm2 0x39, px .xmm3 .xmm6, sld .xmm5 24, mv .xmm6 .xmm4,
  sld .xmm6 24, px .xmm5 .xmm1, px .xmm0 .xmm5, srd .xmm4 8, px .xmm6 .xmm4, px .xmm3 .xmm0, shd .xmm0 .xmm0 0x4e,
  slw .xmm0 .xmm0 0xb1, px .xmm2 .xmm6, ld .xmm1 8, px .xmm7 .xmm1, ld .xmm4 0, sv 4 .xmm7, shd .xmm7 .xmm4 0x39,
  shw .xmm0 .xmm0 0xb1, px .xmm0 .xmm5, mv .xmm5 .xmm7, sld .xmm5 24, srd .xmm7 8, px .xmm5 .xmm7,
  shd .xmm7 .xmm2 0x4e, slw .xmm7 .xmm7 0xb1, shw .xmm7 .xmm7 0xb1, px .xmm7 .xmm6, px .xmm4 .xmm5, px .xmm2 .xmm0,
  shd .xmm0 .xmm4 0x4e, slw .xmm0 .xmm0 0xb1, shw .xmm0 .xmm0 0xb1, px .xmm0 .xmm5, px .xmm7 .xmm4, px .xmm0 .xmm1,
  px .xmm3 .xmm1, px .xmm1 .xmm7]

/-- The round key, InvMixColumns in form 0, and ShiftRows twice, from `invSubOut` to `mid`. -/
def invLinB : List Instr := [
  lk .xmm7 3, px .xmm0 .xmm7, lk .xmm7 5, px .xmm1 .xmm7, lk .xmm7 1, px .xmm2 .xmm7, shd .xmm7 .xmm2 0x4e,
  px .xmm7 .xmm2, px .xmm7 .xmm0, sv 0 .xmm2, lk .xmm2 7, px .xmm4 .xmm2, lk .xmm2 6, px .xmm3 .xmm2, lk .xmm2 2,
  px .xmm5 .xmm2, shd .xmm2 .xmm0 0x4e, px .xmm0 .xmm2, shd .xmm2 .xmm1 0x4e, px .xmm2 .xmm1, px .xmm2 .xmm4,
  sv 1 .xmm7, lk .xmm7 4, px .xmm6 .xmm7, px .xmm1 .xmm0, shd .xmm0 .xmm2 0x39, px .xmm2 .xmm0,
  shd .xmm7 .xmm4 0x4e, px .xmm4 .xmm7, shd .xmm7 .xmm2 0x4e, sv 2 .xmm2, shd .xmm2 .xmm6 0x4e, px .xmm1 .xmm4,
  px .xmm7 .xmm0, px .xmm2 .xmm6, px .xmm2 .xmm3, shd .xmm0 .xmm2 0x39, px .xmm2 .xmm0, px .xmm7 .xmm2,
  slw .xmm7 .xmm7 0xb4, shw .xmm7 .xmm7 0xb4, sv 7 .xmm7, shd .xmm7 .xmm1 0x39, shd .xmm2 .xmm2 0x4e,
  px .xmm1 .xmm7, px .xmm0 .xmm2, shd .xmm2 .xmm5 0x4e, px .xmm2 .xmm5, px .xmm0 .xmm1, shd .xmm1 .xmm1 0x4e,
  slw .xmm0 .xmm0 0xb4, px .xmm1 .xmm7, shw .xmm0 .xmm0 0xb4, px .xmm6 .xmm2, ld .xmm2 15, lk .xmm7 0,
  px .xmm7 .xmm2, shd .xmm2 .xmm7 0x4e, px .xmm2 .xmm7, sv 6 .xmm0, shd .xmm0 .xmm3 0x4e, px .xmm0 .xmm3,
  px .xmm7 .xmm0, px .xmm2 .xmm5, ld .xmm3 1, px .xmm3 .xmm0, px .xmm0 .xmm4, px .xmm6 .xmm0, shd .xmm5 .xmm6 0x39,
  px .xmm6 .xmm5, px .xmm2 .xmm4, px .xmm1 .xmm6, ld .xmm4 0, px .xmm0 .xmm4, shd .xmm4 .xmm3 0x39,
  slw .xmm1 .xmm1 0xb4, shw .xmm1 .xmm1 0xb4, sv 5 .xmm1, shd .xmm1 .xmm2 0x39, px .xmm2 .xmm1, px .xmm3 .xmm4,
  shd .xmm6 .xmm6 0x4e, px .xmm5 .xmm6, px .xmm5 .xmm3, shd .xmm6 .xmm7 0x39, shd .xmm3 .xmm3 0x4e, px .xmm3 .xmm4,
  px .xmm3 .xmm2, shd .xmm4 .xmm0 0x39, shd .xmm2 .xmm2 0x4e, px .xmm0 .xmm4, px .xmm2 .xmm1, shd .xmm1 .xmm0 0x4e,
  px .xmm7 .xmm6, px .xmm1 .xmm4, shd .xmm4 .xmm7 0x4e, px .xmm1 .xmm7, px .xmm2 .xmm0, slw .xmm2 .xmm2 0xb4,
  ld .xmm0 2, px .xmm5 .xmm0, px .xmm3 .xmm0, slw .xmm3 .xmm3 0xb4, px .xmm1 .xmm0, slw .xmm1 .xmm1 0xb4,
  shw .xmm3 .xmm3 0xb4, shw .xmm2 .xmm2 0xb4, px .xmm6 .xmm4, shw .xmm1 .xmm1 0xb4, slw .xmm5 .xmm5 0xb4,
  px .xmm0 .xmm6, slw .xmm0 .xmm0 0xb4, shw .xmm5 .xmm5 0xb4, shw .xmm0 .xmm0 0xb4, sv 4 .xmm5]

/-! ## Between bytes and slices -/

/-- `d` filled with the doubleword `v`, through `ecx`. -/
def fill (d : XReg) (v : BitVec 32) : List Instr := [movI .ecx v, .xop (.movd d .ecx), shd d d 0x00]

/-- Exchange the bits of `lo` `n` above those of the mask in `m` with those
of `hi` at the mask's, through `t`. -/
def swapMove (lo hi t m : XReg) (n : Nat) : List Instr :=
  [mv t lo, srq t n, px t hi, an t m, px hi t, slq t n, px lo t]

/-- The bytes of two blocks, `a` and `b`, each from column by column to row by
row, or back, in place, through `t`. In the numbers of the bytes and of the registers,
in binary, the unpackings rotate the bits of the number of the word, or the
doubleword, through that of the register, and the exchange moves the lowest
bit of the byte's number. The mask `m` is of the even bytes. -/
def bytesPair (a b t m : XReg) : List Instr :=
  [mv t a, lwd a b, hwd t b, mv b a, lwd a t, hwd b t] ++ swapMove a b t m 8 ++
  [mv t a, ldq a b, hdq t b, mv b a, lqdq a t, hqdq b t]

/-- Four blocks in slots `4 g …`, with the word at `kp` added, with their
bytes row by row, then the two lowest bits of the numbers of the bit and of
the block exchanged: the masks are in `xmm5`–`xmm7`. -/
def toGroup (g : Nat) : List Instr :=
  [ld .xmm0 (4 * g), ld .xmm1 (4 * g + 1), ld .xmm2 (4 * g + 2), ld .xmm3 (4 * g + 3), lk .xmm4 0,
   px .xmm0 .xmm4, px .xmm1 .xmm4, px .xmm2 .xmm4, px .xmm3 .xmm4] ++
  bytesPair .xmm0 .xmm1 .xmm4 .xmm5 ++ bytesPair .xmm2 .xmm3 .xmm4 .xmm5 ++
  swapMove .xmm0 .xmm1 .xmm4 .xmm6 1 ++ swapMove .xmm2 .xmm3 .xmm4 .xmm6 1 ++
  swapMove .xmm0 .xmm2 .xmm4 .xmm7 2 ++ swapMove .xmm1 .xmm3 .xmm4 .xmm7 2 ++
  [sv (4 * g) .xmm0, sv (4 * g + 1) .xmm1, sv (4 * g + 2) .xmm2, sv (4 * g + 3) .xmm3]

/-- ShiftRows twice, on a slice. -/
def sr2 (d : XReg) : List Instr := [slw d d 0xb4, shw d d 0xb4]

/-- The third bit of the numbers exchanged, with the mask in `xmm6`, leaving
the slices at `mid`; with ShiftRows twice if `inv`. -/
def toPairs (inv : Bool) : List Instr :=
  [(0, XReg.xmm0), (1, .xmm1), (2, .xmm2), (3, .xmm3)].flatMap fun (i, r) =>
    [ld r i, ld .xmm4 (i + 4)] ++ swapMove r .xmm4 .xmm5 .xmm6 4 ++
    (if inv then sr2 r ++ sr2 .xmm4 else []) ++ [sv (i + 4) .xmm4]

/-- The eight blocks in slots `0 … 7`, with the word at `kp` added, to slices at `mid`. -/
def toMasks : List Instr := fill .xmm5 0x00FF00FF ++ fill .xmm6 0x55555555 ++ fill .xmm7 0x33333333
def toGroups : List Instr := toGroup 0 ++ toGroup 1
def pairMask : List Instr := fill .xmm6 0x0F0F0F0F

/-- The slices where an S-box leaves them to their slots. -/
def toSlots (out : Nat → Loc) : List Instr :=
  ([1, 2, 3, 4, 5, 6, 7].flatMap fun j => match out j with | .x r => [sv j r] | .m _ => []) ++
  (match out 0 with | .m k => [ld .xmm7 k, sv 0 .xmm7] | .x _ => [])

/-- `toPairs`'s inverse, on slots; with ShiftRows twice if `enc`. -/
def fromPairs (enc : Bool) : List Instr :=
  [0, 1, 2, 3].flatMap fun i =>
    [ld .xmm0 i, ld .xmm1 (i + 4)] ++ (if enc then sr2 .xmm0 ++ sr2 .xmm1 else []) ++
    swapMove .xmm0 .xmm1 .xmm2 .xmm6 4 ++ [sv i .xmm0, sv (i + 4) .xmm1]

/-- `toGroup`'s inverse, with the word at `kp` added to the blocks. -/
def fromGroup (g : Nat) : List Instr :=
  [ld .xmm0 (4 * g), ld .xmm1 (4 * g + 1), ld .xmm2 (4 * g + 2), ld .xmm3 (4 * g + 3)] ++
  swapMove .xmm0 .xmm2 .xmm4 .xmm7 2 ++ swapMove .xmm1 .xmm3 .xmm4 .xmm7 2 ++
  swapMove .xmm0 .xmm1 .xmm4 .xmm6 1 ++ swapMove .xmm2 .xmm3 .xmm4 .xmm6 1 ++
  bytesPair .xmm0 .xmm1 .xmm4 .xmm5 ++ bytesPair .xmm2 .xmm3 .xmm4 .xmm5 ++
  [lk .xmm4 0, px .xmm0 .xmm4, px .xmm1 .xmm4, px .xmm2 .xmm4, px .xmm3 .xmm4,
   sv (4 * g) .xmm0, sv (4 * g + 1) .xmm1, sv (4 * g + 2) .xmm2, sv (4 * g + 3) .xmm3]

def fromMasks : List Instr := fill .xmm5 0x00FF00FF ++ fill .xmm6 0x55555555 ++ fill .xmm7 0x33333333
def fromGroups : List Instr := fromGroup 0 ++ fromGroup 1

/-! ## The round keys -/

/-- Where the round keys of the rounds 1 to `R - 1` are. -/
def keysOff : Nat := 384

/-- The last round key, with `{63}` added, is in this slot. -/
def lastSlot : Nat := 18

/-- The constants of the key setup, in slots `0 … 5`: a doubleword, and the
shuffle that makes the 16 bytes of it and zeros. -/
def keyConsts : List (Nat × BitVec 32 × BitVec 8) :=
  [(0, 0x0F0F0F0F, 0x00), (1, 0x33333333, 0x00), (2, 0x55555555, 0x00), (3, 0xFF00FF00, 0x44),
   (4, 0xFFFFFFFF, 0x11), (5, 0x63636363, 0x00)]

def keyMasks : List Instr :=
  keyConsts.flatMap fun (k, v, o) => [movI .ecx v, .xop (.movd .xmm0 .ecx), shd .xmm0 .xmm0 o, sv k .xmm0]

/-- `x`'s bits whose mask is `m` to `a`, and the others to `x`, each copied
to the place of the other, `n` away, through `t`. -/
def split (x a t m : XReg) (n : Nat) : List Instr :=
  [mv a x, an a m, px x a, mv t a, slq t n, px a t, mv t x, srq t n, px x t]

/-- A round key's bytes (in `xmm0`), with `{63}` added, row by row: a row's
columns rotated by its number if `odd` (form 1). -/
def keyBytes (odd : Bool) : List Instr :=
  [ld .xmm1 5, px .xmm0 .xmm1,
   shd .xmm0 .xmm0 0xd8, slw .xmm0 .xmm0 0xd8, shw .xmm0 .xmm0 0xd8, shd .xmm0 .xmm0 0xd8,
   ld .xmm2 3, mv .xmm1 .xmm0, srq .xmm1 24, px .xmm1 .xmm0, an .xmm1 .xmm2, px .xmm0 .xmm1, slq .xmm1 24,
   px .xmm0 .xmm1] ++
  if odd then
    [shw .xmm0 .xmm0 0xb1, ld .xmm3 4, mv .xmm1 .xmm0, sld .xmm1 8, mv .xmm2 .xmm0, srd .xmm2 24, px .xmm1 .xmm2,
     px .xmm1 .xmm0, an .xmm1 .xmm3, px .xmm0 .xmm1]
  else []

/-- Where the slices of the round key go. -/
def dp : Reg := .edx
def sk (k : Nat) (s : XReg) : Instr := .movdquStore (at_ dp (16 * k)) s

/-- Each bit copied over its byte: halves, quarters, eighths. -/
def keySlices : List Instr :=
  [ld .xmm5 0, ld .xmm6 1, ld .xmm7 2] ++ split .xmm0 .xmm1 .xmm4 .xmm5 4 ++
  [(XReg.xmm1, 0), (.xmm0, 4)].flatMap fun (x, b) =>
    split x .xmm2 .xmm4 .xmm6 2 ++
    split .xmm2 .xmm3 .xmm4 .xmm7 1 ++ [sk b .xmm3, sk (b + 1) .xmm2] ++
    split x .xmm3 .xmm4 .xmm7 1 ++ [sk (b + 2) .xmm3, sk (b + 3) x]

/-- The round key at `kp` to the slices at `dp`, and on to the next. -/
def keyOne (odd : Bool) : List Instr :=
  lk .xmm0 0 :: (keyBytes odd ++ keySlices ++ [addI kp 16, addI dp 128])

/-- Round keys 1 to `R - 1`, in pairs but the last, and the last round key. -/
def keys : Prog isa :=
  .seq (.block (keyMasks ++ [.mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)), movR .edx .ecx] ++ dbl .edx 4 ++
      [addR .edx .eax, .movdquLoad .xmm0 (at_ .edx 0), ld .xmm1 5, px .xmm0 .xmm1, sv lastSlot .xmm0,
       shrI .ecx 1, addI .eax 16, movR .edx .edi, addI .edx (BitVec.ofNat 32 keysOff)]))
    (.loop (.seq (.block (keyOne true ++ [subI .ecx 1]))
      (.ite .e (.block []) (.block (keyOne false ++ [.alu .test .ecx (.reg .ecx)])))) .ne)

/-! ## Eight blocks -/

/-- `kp` at the round keys from the first, or from the last, and `ecx` half the rounds. -/
def encStart : List Instr :=
  [.mov .ecx (.mem (argOp 1)), shrI .ecx 1, movR .eax .edi, addI .eax (BitVec.ofNat 32 keysOff)]
def decStart : List Instr :=
  [.mov .ecx (.mem (argOp 1)), movR .eax .ecx] ++ dbl .eax 7 ++
  [addR .eax .edi, addI .eax (BitVec.ofNat 32 (keysOff - 256)), shrI .ecx 1]

/-- The rounds, in pairs but the last: `ecx` is the number of the first ones. -/
def rounds (a b : List Instr) (step : Instr) : Prog isa :=
  .loop (.seq (.block (a ++ [step, subI .ecx 1]))
    (.ite .e (.block []) (.block (b ++ [step, .alu .test .ecx (.reg .ecx)])))) .ne

/-- `kp` at the plain round key 0, or the last with `{63}` added. -/
def firstKey : Instr := .mov .eax (.mem (argOp 0))
def lastKey : List Instr := [movR .eax .edi, addI .eax (BitVec.ofNat 32 (16 * lastSlot))]

/-- The eight blocks in slots `0 … 7`, in place. -/
def encrypt8 : Prog isa :=
  .seq (.block (firstKey :: toMasks ++ toGroups ++ pairMask ++ toPairs false ++ encStart))
    (.seq (rounds (subBytes ++ linA) (subBytes ++ linB) (addI kp 128))
      (.block (subBytes ++ toSlots subOut ++ lastKey ++ pairMask ++ fromPairs true ++ fromMasks ++ fromGroups)))

def decrypt8 : Prog isa :=
  .seq (.block (lastKey ++ toMasks ++ toGroups ++ pairMask ++ toPairs true ++ decStart))
    (.seq (rounds (invSubBytes ++ invLinA) (invSubBytes ++ invLinB) (subI kp 128))
      (.block (invSubBytes ++ toSlots invSubOut ++ firstKey :: pairMask ++ fromPairs false ++ fromMasks ++
        fromGroups)))

/-! ## The functions' entry and exit -/

/-- The callee-saved registers, and their offsets in the scratch buffer. -/
def savedRegs : List (Reg × Nat) := [(.ebx, 304), (.esi, 308), (.edi, 312), (.ebp, 316)]

/-- Load the scratch pointer (argument `k`) into `edi`, saving the registers. -/
def saveRegs (k : Nat) : List Instr :=
  .mov .eax (.mem (argOp k)) :: (savedRegs.map fun (r, d) => .store (at_ .eax d) r) ++ [movR .edi .eax]

def restoreRegs : List Instr :=
  [.mov .ebx (.mem (at_ .edi 304)), .mov .esi (.mem (at_ .edi 308)), .mov .ebp (.mem (at_ .edi 316)),
   .mov .edi (.mem (at_ .edi 312))]

/-! ## Whole blocks

`ebx` is the data and `ebp` the number of blocks left, of which a batch
takes `ecx`: up to eight, the rest of the slots keeping what is there. -/

/-- `ecx ≔ min 8 ebp`. -/
def takeCount : Prog isa :=
  .seq (.block [.alu .cmp .ebp (.imm 8)]) (.ite .ae (.block [movI .ecx 8]) (.block [movR .ecx .ebp]))

/-- A block copied, through `xmm0`. -/
def copyBody (src dst : Reg) : List Instr :=
  [.movdquLoad .xmm0 (at_ src 0), .movdquStore (at_ dst 0) .xmm0, addI src 16, addI dst 16, subI .ecx 1]

def copyIn : Prog isa :=
  .seq (.block [movR .esi .ebx, movR .edx .edi]) (.seq takeCount (.loop (.block (copyBody .esi .edx)) .ne))

def copyOut : Prog isa :=
  .seq (.block [movR .edx .edi]) (.seq takeCount (.seq (.block [subR .ebp .ecx])
    (.seq (.loop (.block (copyBody .edx .ebx)) .ne) (.block [.alu .test .ebp (.reg .ebp)]))))

def blockGroup (crypt8 : Prog isa) : Prog isa := .seq copyIn (.seq crypt8 copyOut)

/-- `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`. -/
def blocks (crypt8 : Prog isa) : Prog isa :=
  .seq (.block (saveRegs 4)) (.seq keys
    (.seq (.block [.mov .ebx (.mem (argOp 2)), .mov .ebp (.mem (argOp 3)), .alu .test .ebp (.reg .ebp)])
      (.seq (.ite .e (.block []) (.loop (blockGroup crypt8) .ne)) (.block restoreRegs))))

def encryptBlocks : Prog isa := blocks encrypt8
def decryptBlocks : Prog isa := blocks decrypt8

/-! ## Counter mode

`edx` is the source, `ebx` the destination and `ebp` the number of blocks
left. -/

/-- The counter block's first three words, and the counter as a number. -/
def ctrOff : Nat := 320
def cNum : Nat := 332

/-- The counter block to the scratch buffer, and the counter `n` blocks on back. -/
def ctrSetup : List Instr :=
  [.mov .ecx (.mem (argOp 2)), .mov .eax (.mem (at_ .ecx 0)), .store (at_ .edi ctrOff) .eax,
   .mov .eax (.mem (at_ .ecx 4)), .store (at_ .edi (ctrOff + 4)) .eax, .mov .eax (.mem (at_ .ecx 8)),
   .store (at_ .edi (ctrOff + 8)) .eax, .mov .eax (.mem (at_ .ecx 12)), .bswap .eax, .store (at_ .edi cNum) .eax,
   .alu .add .eax (.mem (argOp 4)), .bswap .eax, .store (at_ .ecx 12) .eax]

/-- Counter block `j` of the batch to its slot: the counter's bytes after
the twelve in `xmm1`. -/
def ctrBlock (j : Nat) : List Instr :=
  [movR .eax .esi, addI .eax (BitVec.ofNat 32 j), .bswap .eax, .xop (.movd .xmm0 .eax),
   .xop (.shift .pslldq .xmm0 12), .xop (.bin .por .xmm0 .xmm1), sv j .xmm0]

def ctrBlocks : List Instr :=
  [.movdquLoad .xmm1 (at_ .edi ctrOff), .xop (.shift .pslldq .xmm1 4), .xop (.shift .psrldq .xmm1 4),
   .mov .esi (.mem (at_ .edi cNum))] ++ (List.range' 0 8).flatMap ctrBlock ++
  [addI .esi 8, .store (at_ .edi cNum) .esi]

/-- A block of the key stream (at `esi`) added to the data. -/
def xorBody : List Instr :=
  [.movdquLoad .xmm0 (at_ .esi 0), .movdquLoad .xmm1 (at_ .edx 0), px .xmm0 .xmm1, .movdquStore (at_ .ebx 0) .xmm0,
   addI .esi 16, addI .edx 16, addI .ebx 16, subI .ecx 1]

def xorOut : Prog isa :=
  .seq (.block [movR .esi .edi]) (.seq takeCount (.seq (.block [subR .ebp .ecx])
    (.seq (.loop (.block xorBody) .ne) (.block [.alu .test .ebp (.reg .ebp)]))))

def group : Prog isa := .seq (.block ctrBlocks) (.seq encrypt8 xorOut)

def ctrPtrs : List Instr :=
  [.mov .edx (.mem (argOp 3)), .mov .ebx (.mem (argOp 6)), .mov .ebp (.mem (argOp 4)), .alu .test .ebp (.reg .ebp)]

/-- `vg_aes_ctr32_to`. -/
def ctr32To : Prog isa :=
  .seq (.block (saveRegs 5 ++ ctrSetup)) (.seq keys (.seq (.block ctrPtrs)
    (.seq (.ite .e (.block []) (.loop group .ne)) (.block restoreRegs))))

end VG.Impl.Aes.X86.Sse
