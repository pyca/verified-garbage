module

public import VerifiedGarbage.Impl.Aes.X86_64.Linear

/-!
# Bitsliced AES on x86-64, eight blocks at a time in SSE2 registers

A register is two quadwords that never mix while the cipher runs, each the
slices of four blocks: bit `j` of the byte in row `r` and column `c` of
block `k` is at bit `k + 4 (c + 4 r)` of slice `j` (`toBs`). So rows are
rotated by rotating quadwords by 16 bits, and columns, of all rows at once,
by rotating 16-bit words by 4.

**ShiftRows is not done.** A round that leaves every byte where it is leaves
the byte of row `r` and column `c` at column `c + r` (form 1 of the state,
where form 0 is the plain one), which the next layers allow for: MixColumns
of form 1 takes the next row's byte one column further, and its round key is
stored in form 1 (`toForm1`). The round after does ShiftRows twice (`sr2`:
only the odd rows move, by two columns), which gives form 0 again. The
numbers of rounds are even, so rounds go in pairs: `roundA` from form 0 to 1
and `roundB` back. The inverse cipher's pair starts with `sr2`, which from
form 0 gives InvShiftRows in form 1, and ends with none.

**The S-box's constant is in the round keys.** `{63}` in every byte goes
through ShiftRows and MixColumns unchanged (`2 + 3 + 1 + 1 = 1`), so the
round keys but the first have it added (`complement`), and `subBytes`
computes the S-box without it; likewise `invSubBytes` takes its input with
it added.

The scratch buffer (at `r9`), in 16-byte slots: the round keys (0–59), 64
bytes each, a quadword per slice; the S-boxes' spills (60–68); masks
(69–75); the eight blocks of a batch (76–83); and working space of
InvMixColumns (84–91). 1472 bytes in all.
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64.Sse

open VG.X86_64

/-! ## Registers, slots and short forms -/

/-- Slice `j`, before SubBytes; after it, it is in `p j`. -/
def q : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3
  | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | _ => .xmm7

def p : Nat → XReg
  | 0 => .xmm8 | 1 => .xmm9 | 2 => .xmm10 | 3 => .xmm11
  | 4 => .xmm12 | 5 => .xmm13 | 6 => .xmm14 | _ => .xmm15

/-- Slot `k` of the scratch buffer. -/
def slot (k : Nat) : MemOp := { base := .r9, disp := ((16 * k : Nat) : Int) }

def spillSlot (k : Nat) : Nat := 60 + k
/-- The masks of `toBs`'s exchanges, by the place value of the index bit. -/
def maskSlot (i : Nat) : Nat := 69 + i
def sr2Slot : Nat := 75
def bufSlot (b : Nat) : Nat := 76 + b
def tmpSlot (j : Nat) : Nat := 84 + j

def mv (d s : XReg) : Instr := .xop (.bin .movdqa d s)
def px (d s : XReg) : Instr := .xop (.bin .pxor d s)
def an (d s : XReg) : Instr := .xop (.bin .pand d s)
def srq (d : XReg) (n : Nat) : Instr := .xop (.shift .psrlq d (BitVec.ofNat 8 n))
def slq (d : XReg) (n : Nat) : Instr := .xop (.shift .psllq d (BitVec.ofNat 8 n))
def srw (d : XReg) (n : Nat) : Instr := .xop (.shift .psrlw d (BitVec.ofNat 8 n))
def slw (d : XReg) (n : Nat) : Instr := .xop (.shift .psllw d (BitVec.ofNat 8 n))
def ldx (d : XReg) (k : Nat) : Instr := .movdquLoad d (slot k)
def stx (k : Nat) (s : XReg) : Instr := .movdquStore (slot k) s
/-- A spill, and its reload. -/
def sv (k : Nat) (s : XReg) : Instr := stx (spillSlot k) s
def ld (d : XReg) (k : Nat) : Instr := ldx d (spillSlot k)

/-! ## SubBytes -/

/-- `Circuit.sbox` without its constant, from `q j` to `p j`: the circuit in
an order that needs few spills, allocated to the sixteen registers. -/
def subBytes : List Instr := [
  px .xmm2 .xmm5, mv .xmm8 .xmm2, px .xmm8 .xmm1, mv .xmm9 .xmm8, px .xmm9 .xmm6,
  px .xmm3 .xmm9, px .xmm3 .xmm7, px .xmm0 .xmm8, mv .xmm10 .xmm3, px .xmm10 .xmm2,
  mv .xmm11 .xmm10, px .xmm11 .xmm0, px .xmm5 .xmm11, mv .xmm12 .xmm5, px .xmm12 .xmm7,
  mv .xmm13 .xmm11, px .xmm13 .xmm9, mv .xmm14 .xmm11, px .xmm14 .xmm4, mv .xmm15 .xmm14,
  an .xmm15 .xmm11, sv 0 .xmm11, mv .xmm11 .xmm14, px .xmm11 .xmm12, sv 1 .xmm5,
  mv .xmm5 .xmm14, px .xmm5 .xmm3, px .xmm3 .xmm4, sv 2 .xmm14, mv .xmm14 .xmm12,
  an .xmm14 .xmm9, sv 3 .xmm9, mv .xmm9 .xmm11, an .xmm9 .xmm13, sv 4 .xmm11, mv .xmm11 .xmm12,
  px .xmm11 .xmm6, px .xmm4 .xmm10, sv 5 .xmm12, mv .xmm12 .xmm4, an .xmm12 .xmm5,
  px .xmm9 .xmm12, sv 6 .xmm5, mv .xmm5 .xmm7, an .xmm5 .xmm8, px .xmm12 .xmm14,
  px .xmm5 .xmm15, px .xmm5 .xmm12, mv .xmm14 .xmm0, px .xmm14 .xmm7, px .xmm1 .xmm4,
  px .xmm5 .xmm11, mv .xmm11 .xmm0, an .xmm11 .xmm3, px .xmm12 .xmm11, sv 7 .xmm0,
  mv .xmm0 .xmm14, an .xmm0 .xmm1, px .xmm0 .xmm9, px .xmm0 .xmm15, px .xmm0 .xmm2, ld .xmm15 1,
  mv .xmm2 .xmm15, an .xmm2 .xmm6, sv 8 .xmm6, mv .xmm6 .xmm15, px .xmm6 .xmm8, px .xmm12 .xmm2,
  px .xmm12 .xmm6, mv .xmm2 .xmm4, px .xmm2 .xmm15, mv .xmm6 .xmm13, px .xmm6 .xmm1,
  mv .xmm15 .xmm2, an .xmm15 .xmm6, px .xmm9 .xmm15, px .xmm9 .xmm11, mv .xmm15 .xmm5,
  an .xmm15 .xmm0, px .xmm9 .xmm10, mv .xmm11 .xmm12, px .xmm11 .xmm15, px .xmm15 .xmm9,
  mv .xmm10 .xmm0, px .xmm10 .xmm9, an .xmm11 .xmm10, px .xmm5 .xmm12, px .xmm11 .xmm9,
  px .xmm0 .xmm11, mv .xmm10 .xmm15, px .xmm10 .xmm11, an .xmm9 .xmm10, px .xmm0 .xmm9,
  an .xmm8 .xmm11, px .xmm9 .xmm15, an .xmm15 .xmm5, px .xmm12 .xmm15, an .xmm9 .xmm12,
  px .xmm9 .xmm5, ld .xmm10 4, an .xmm10 .xmm9, an .xmm7 .xmm11, mv .xmm15 .xmm12,
  px .xmm15 .xmm9, an .xmm6 .xmm15, an .xmm1 .xmm12, an .xmm14 .xmm12, an .xmm13 .xmm9,
  px .xmm12 .xmm11, px .xmm6 .xmm13, an .xmm15 .xmm2, px .xmm13 .xmm1, an .xmm3 .xmm12,
  px .xmm11 .xmm0, px .xmm9 .xmm0, ld .xmm5 7, an .xmm5 .xmm12, ld .xmm2 3, an .xmm2 .xmm0,
  px .xmm2 .xmm8, px .xmm5 .xmm15, px .xmm3 .xmm6, px .xmm12 .xmm9, ld .xmm1 5, an .xmm0 .xmm1,
  ld .xmm1 6, an .xmm1 .xmm12, px .xmm15 .xmm7, an .xmm12 .xmm4, px .xmm6 .xmm1, ld .xmm4 2,
  an .xmm4 .xmm9, px .xmm13 .xmm2, px .xmm12 .xmm10, px .xmm4 .xmm12, px .xmm5 .xmm12,
  px .xmm5 .xmm13, px .xmm15 .xmm4, px .xmm4 .xmm14, px .xmm14 .xmm5, px .xmm6 .xmm8,
  ld .xmm12 1, an .xmm12 .xmm11, px .xmm1 .xmm4, px .xmm14 .xmm0, px .xmm13 .xmm4, ld .xmm8 8,
  an .xmm11 .xmm8, px .xmm14 .xmm10, px .xmm2 .xmm1, px .xmm6 .xmm11, ld .xmm0 0,
  an .xmm9 .xmm0, px .xmm2 .xmm9, px .xmm14 .xmm7, px .xmm15 .xmm12, px .xmm1 .xmm15,
  px .xmm6 .xmm9, px .xmm1 .xmm3, mv .xmm8 .xmm5, mv .xmm9 .xmm4, mv .xmm10 .xmm15,
  mv .xmm11 .xmm6, mv .xmm12 .xmm14, mv .xmm14 .xmm1, mv .xmm15 .xmm2]

/-- The inverse S-box's circuit, of an input with `{63}` added, from `q j`
to `p j`. -/
def invSubBytes : List Instr := [
  mv .xmm8 .xmm5, px .xmm8 .xmm4, px .xmm1 .xmm8, mv .xmm9 .xmm1, px .xmm9 .xmm6,
  px .xmm5 .xmm9, px .xmm3 .xmm1, px .xmm6 .xmm7, mv .xmm10 .xmm3, px .xmm10 .xmm5,
  mv .xmm11 .xmm4, px .xmm11 .xmm2, mv .xmm12 .xmm11, px .xmm12 .xmm0, mv .xmm13 .xmm10,
  px .xmm13 .xmm7, px .xmm0 .xmm6, mv .xmm14 .xmm9, px .xmm14 .xmm0, mv .xmm15 .xmm5,
  an .xmm15 .xmm0, sv 0 .xmm5, mv .xmm5 .xmm3, an .xmm5 .xmm9, px .xmm4 .xmm0, sv 1 .xmm0,
  mv .xmm0 .xmm10, an .xmm0 .xmm14, sv 2 .xmm14, mv .xmm14 .xmm3, px .xmm14 .xmm4, sv 3 .xmm10,
  mv .xmm10 .xmm1, px .xmm10 .xmm2, sv 4 .xmm3, mv .xmm3 .xmm14, an .xmm3 .xmm13,
  px .xmm0 .xmm5, px .xmm15 .xmm5, px .xmm3 .xmm0, px .xmm6 .xmm12, px .xmm7 .xmm10,
  mv .xmm5 .xmm7, px .xmm5 .xmm14, sv 5 .xmm14, mv .xmm14 .xmm5, an .xmm14 .xmm6,
  px .xmm3 .xmm14, sv 6 .xmm5, mv .xmm5 .xmm13, px .xmm5 .xmm9, px .xmm14 .xmm15, sv 7 .xmm9,
  mv .xmm9 .xmm13, px .xmm9 .xmm6, sv 8 .xmm6, mv .xmm6 .xmm7, an .xmm6 .xmm9, px .xmm14 .xmm6,
  mv .xmm6 .xmm5, px .xmm6 .xmm11, px .xmm3 .xmm10, px .xmm10 .xmm13, px .xmm14 .xmm2,
  mv .xmm2 .xmm10, an .xmm2 .xmm6, px .xmm15 .xmm2, px .xmm1 .xmm9, mv .xmm2 .xmm1,
  an .xmm2 .xmm11, px .xmm15 .xmm2, px .xmm0 .xmm2, mv .xmm2 .xmm4, an .xmm2 .xmm5,
  px .xmm0 .xmm2, px .xmm15 .xmm12, px .xmm0 .xmm8, mv .xmm2 .xmm15, an .xmm2 .xmm14,
  mv .xmm12 .xmm14, px .xmm12 .xmm3, mv .xmm8 .xmm0, px .xmm8 .xmm2, px .xmm15 .xmm0,
  an .xmm8 .xmm12, px .xmm2 .xmm3, px .xmm8 .xmm3, px .xmm14 .xmm8, mv .xmm12 .xmm2,
  px .xmm12 .xmm8, an .xmm3 .xmm12, an .xmm1 .xmm8, px .xmm14 .xmm3, mv .xmm12 .xmm14,
  px .xmm12 .xmm8, px .xmm3 .xmm2, an .xmm5 .xmm14, an .xmm2 .xmm15, an .xmm4 .xmm14,
  px .xmm0 .xmm2, an .xmm6 .xmm12, an .xmm3 .xmm0, ld .xmm2 8, an .xmm2 .xmm0, px .xmm3 .xmm15,
  an .xmm11 .xmm8, ld .xmm15 5, an .xmm15 .xmm3, an .xmm12 .xmm10, px .xmm8 .xmm0,
  px .xmm14 .xmm3, an .xmm13 .xmm3, px .xmm3 .xmm0, an .xmm9 .xmm3, ld .xmm10 6,
  an .xmm0 .xmm10, an .xmm3 .xmm7, ld .xmm10 0, an .xmm10 .xmm8, px .xmm10 .xmm12,
  mv .xmm7 .xmm2, px .xmm7 .xmm5, px .xmm12 .xmm4, px .xmm11 .xmm15, px .xmm11 .xmm7,
  px .xmm12 .xmm3, ld .xmm7 4, an .xmm7 .xmm14, px .xmm10 .xmm7, px .xmm11 .xmm13,
  px .xmm0 .xmm11, px .xmm10 .xmm1, ld .xmm3 7, an .xmm3 .xmm14, px .xmm14 .xmm8,
  px .xmm4 .xmm0, px .xmm15 .xmm12, px .xmm4 .xmm1, px .xmm3 .xmm9, ld .xmm1 1, an .xmm8 .xmm1,
  px .xmm8 .xmm4, ld .xmm1 3, an .xmm1 .xmm14, px .xmm1 .xmm7, ld .xmm7 2, an .xmm14 .xmm7,
  px .xmm1 .xmm0, px .xmm14 .xmm8, px .xmm6 .xmm10, px .xmm8 .xmm2, px .xmm8 .xmm3,
  px .xmm5 .xmm14, px .xmm14 .xmm13, px .xmm12 .xmm11, px .xmm15 .xmm8, px .xmm5 .xmm6,
  px .xmm14 .xmm9, px .xmm8 .xmm5, mv .xmm9 .xmm8, mv .xmm8 .xmm4, mv .xmm11 .xmm10,
  mv .xmm10 .xmm12, mv .xmm12 .xmm14, mv .xmm13 .xmm1, mv .xmm14 .xmm5]

/-! ## Bytes to slices -/

/-- Exchange the bits of `lo` `n` above those of the mask in `m` with those
of `hi` at the mask's. -/
def swapMove (lo hi t m : XReg) (n : Nat) : List Instr :=
  [mv t lo, srq t n, px t hi, an t m, px hi t, slq t n, px lo t]

/-- The mask of the positions whose index bit of place value `2 ^ i` is 0. -/
def idxMask (i : Nat) : BitVec 64 :=
  match i with
  | 0 => 0x5555555555555555 | 1 => 0x3333333333333333 | 2 => 0x0F0F0F0F0F0F0F0F
  | 3 => 0x00FF00FF00FF00FF | 4 => 0x0000FFFF0000FFFF | _ => 0x00000000FFFFFFFF

/-- Exchange bit `b` of the register's number with bit `i` of the position. -/
def exchange (b i : Nat) : List Instr :=
  ldx .xmm9 (maskSlot i) :: ((List.range 8).filter fun k => k / 2 ^ b % 2 == 0).flatMap fun k =>
    swapMove (q k) (q (k + 2 ^ b)) .xmm8 .xmm9 (2 ^ i)

/-- From the halves of four blocks (register `k + 4 c`: columns `2 c` and
`2 c + 1` of block `k`) to slices. -/
def toBs : List Instr :=
  exchange 2 3 ++ exchange 2 4 ++ exchange 2 5 ++ exchange 2 2 ++ exchange 1 1 ++ exchange 0 0

def fromBs : List Instr :=
  exchange 0 0 ++ exchange 1 1 ++ exchange 2 2 ++ exchange 2 5 ++ exchange 2 4 ++ exchange 2 3

/-- The masks' constants into their slots, through `rax` and `xmm0`. -/
def setMask (k : Nat) (v : BitVec 64) : List Instr :=
  [.movImm64 .rax v, .xop (.movq .xmm0 .rax), .xop (.bin .punpcklqdq .xmm0 .xmm0), stx k .xmm0]

def sr2Mask : BitVec 64 := 0x00FF000000FF0000

def setMasks : List Instr :=
  ((List.range 6).flatMap fun i => setMask (maskSlot i) (idxMask i)) ++ setMask sr2Slot sr2Mask

/-! ## Linear layers -/

/-- `d` := `a` with every row's columns rotated by one (`u` is lost). -/
def colRot (d a u : XReg) : List Instr := [mv d a, srw d 4, mv u a, slw u 12, px d u]

/-- `d` := `a` with the rows rotated by one (`u` is lost). -/
def rowRot (d a u : XReg) : List Instr := [mv d a, srq d 16, mv u a, slq u 48, px d u]

/-- The next row's bytes, in form `f`, of `a` to `d`. -/
def nextRow (f : Bool) (d a u v : XReg) : List Instr :=
  if f then colRot v a u ++ [mv d v, srq d 16, slq v 48, px d v] else rowRot d a u

/-- The bytes two rows on, in form `f`, of `a` to `d` (`u` is lost). -/
def row2 (f : Bool) (d a u : XReg) : List Instr :=
  if f then ([.xop (.pshufd d a 0xb1), mv u d, srw d 8, slw u 8, px d u] : List Instr)
  else [.xop (.pshufd d a 0xb1)]

/-- The first half of MixColumns, on slice `j`: `a ⊕ next(a)` in place (`b`),
and `next(a) ⊕ row2(b)` to `o` (`u`, `v` are lost). -/
def mcHalf (f : Bool) (a o u v : XReg) : List Instr :=
  nextRow f o a u v ++ [px a o] ++ row2 f u a v ++ [px o u]

/-- MixColumns in form `f`, from `p j` to `q j`: `b ≔ a ⊕ next(a)`, and the
result is `2 b ⊕ next(a) ⊕ row2(b)`. Slice 7 first, whose `b` the
reduction adds to slices 0, 1, 3 and 4. -/
def mixColumns (f : Bool) : List Instr :=
  mcHalf f (p 7) (q 7) (q 0) (q 1) ++
  mcHalf f (p 0) (q 0) (q 1) (q 2) ++ [px (q 0) (p 7)] ++
  mcHalf f (p 1) (q 1) (q 2) (q 3) ++ [px (q 1) (p 0), px (q 1) (p 7)] ++
  mcHalf f (p 2) (q 2) (q 3) (q 4) ++ [px (q 2) (p 1)] ++
  mcHalf f (p 3) (q 3) (q 4) (q 5) ++ [px (q 3) (p 2), px (q 3) (p 7)] ++
  mcHalf f (p 4) (q 4) (q 5) (q 6) ++ [px (q 4) (p 3), px (q 4) (p 7)] ++
  mcHalf f (p 5) (q 5) (q 6) (p 0) ++ [px (q 5) (p 4)] ++
  mcHalf f (p 6) (q 6) (p 0) (p 1) ++ [px (q 6) (p 5), px (q 7) (p 6)]

/-- ShiftRows twice, on slice `a`: the odd rows rotated by two columns. -/
def sr2One (a t m : XReg) : List Instr :=
  [mv t a, srw t 8, px t a, an t m, px a t, slw t 8, px a t]

/-- ShiftRows twice, on the slices `r j`. -/
def sr2 (r : Nat → XReg) (t m : XReg) : List Instr :=
  ldx m sr2Slot :: (List.range 8).flatMap fun j => sr2One (r j) t m

end VG.Impl.Aes.X86_64.Sse
