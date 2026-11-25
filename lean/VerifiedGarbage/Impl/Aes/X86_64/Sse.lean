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

The scratch buffer (at `r9`), in 16-byte slots: the S-boxes' spills (0–8);
masks (9–17); the eight blocks of a batch (18–25); and the round keys
(26–85), 64 bytes each, a quadword per slice. 1376 bytes in all.
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

def spillSlot (k : Nat) : Nat := k
/-- The masks of `toBs`'s exchanges, by the place value of the index bit. -/
def maskSlot (i : Nat) : Nat := 9 + i
def sr2Slot : Nat := 15
def highSlot : Nat := 16
def oddSlot : Nat := 17
def bufSlot (b : Nat) : Nat := 18 + b
/-- Where the round keys start. -/
def keysOff : Nat := 416

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

/-- Two columns of the rows 2 and 3; the odd rows. -/
def highMask : BitVec 64 := 0x00FF00FF00000000
def oddMask : BitVec 64 := 0xFFFF0000FFFF0000

def setMasks : List Instr :=
  ((List.range 6).flatMap fun i => setMask (maskSlot i) (idxMask i)) ++ setMask sr2Slot sr2Mask ++
    setMask highSlot highMask ++ setMask oddSlot oddMask

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

/-- `y_j ≔ a_j ⊕ row2(a_j)`, of `p j` to `q j` (`u` is lost). -/
def invPre (f : Bool) (j : Nat) (u : XReg) : List Instr := row2 f (q j) (p j) u ++ [px (q j) (p j)]

/-- InvMixColumns in form `f`, from `p j` to `q j`: MixColumns of
`a ⊕ 4 (a ⊕ row2(a))`, since `0b x³ + 0d x² + 09 x + 0e` is
`(03 x³ + x² + x + 02) (04 x² + 05)` modulo `x⁴ + 1`. -/
def invMixColumns (f : Bool) : List Instr :=
  (List.range 7).flatMap (fun j => invPre f j (q 7)) ++
  [px (p 0) (q 6), px (p 1) (q 6), px (p 2) (q 0), px (p 3) (q 1), px (p 3) (q 6), px (p 4) (q 2),
   px (p 4) (q 6), px (p 5) (q 3), px (p 6) (q 4)] ++
  invPre f 7 (q 0) ++
  [px (p 7) (q 5), px (p 1) (q 7), px (p 2) (q 7), px (p 4) (q 7), px (p 5) (q 7)] ++
  mixColumns f

/-! ## Round keys -/

/-- The register of the round key's address. -/
def kp : Reg := .rax

def dupLow (d s : XReg) : Instr := .xop (.pshufd d s 0x44)
def dupHigh (d s : XReg) : Instr := .xop (.pshufd d s 0xee)
def unpckl (d s : XReg) : Instr := .xop (.bin .punpcklqdq d s)
def unpckh (d s : XReg) : Instr := .xop (.bin .punpckhqdq d s)

/-- XOR the round key at `kp`, a quadword for each slice, into both quadwords
of the slices `r j`. -/
def addRoundKey (r : Nat → XReg) (t u : XReg) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.movdquLoad t (at_ kp (16 * i)), dupLow u t, dupHigh t t, px (r (2 * i)) u, px (r (2 * i + 1)) t]

/-- `ShiftRows⁻¹` of slice `a`: from form 0 to form 1 (`t`, `u` are lost; the
masks are in `h` and `o`). -/
def toForm1 (a t u h o : XReg) : List Instr :=
  [mv t a, srw t 8, px t a, an t h, px a t, slw t 8, px a t,
   mv t a, slw t 4, mv u a, srw u 12, px t u, px t a, an t o, px a t]

/-- The halves of two round keys, at `r10`, in their registers: the first key
in the low quadwords and the second in the high ones. -/
def keyLoad2 : List Instr :=
  [.movdquLoad (q 0) (at_ .r10 0), .movdquLoad (q 1) (at_ .r10 16), mv (q 4) (q 0), unpckl (q 0) (q 1),
   unpckh (q 4) (q 1)]

/-- The last round key's halves. -/
def keyLoad1 : List Instr :=
  [.movdquLoad (q 0) (at_ .r10 0), mv (q 4) (q 0), unpckl (q 0) (q 0), unpckh (q 4) (q 4)]

/-- Every block's halves are the key's. -/
def keySpread : List Instr :=
  [mv (q 1) (q 0), mv (q 2) (q 0), mv (q 3) (q 0), mv (q 5) (q 4), mv (q 6) (q 4), mv (q 7) (q 4)]

/-- Store the slices' low quadwords at `kp`. -/
def storeLow : List Instr :=
  (List.range 4).flatMap fun i =>
    [mv .xmm8 (q (2 * i)), unpckl .xmm8 (q (2 * i + 1)), .movdquStore (at_ kp (16 * i)) .xmm8]

/-- Store the slices' high quadwords 64 bytes on. -/
def storeHigh : List Instr :=
  (List.range 4).flatMap fun i =>
    [unpckh (q (2 * i)) (q (2 * i + 1)), .movdquStore (at_ kp (64 + 16 * i)) (q (2 * i))]

/-- All slices to form 1. -/
def form1 : List Instr :=
  [ldx .xmm10 highSlot, ldx .xmm11 oddSlot] ++
    (List.range 8).flatMap fun j => toForm1 (q j) .xmm8 .xmm9 .xmm10 .xmm11

/-- Two round keys: the first in form 0, the second in form 1. -/
def keyBody : List Instr :=
  keyLoad2 ++ (keySpread ++ toBs) ++ storeLow ++ form1 ++ storeHigh ++
    [.alu .add .r10 (.imm 32), .alu .add kp (.imm 128), .alu .sub .rdi (.imm 1)]

/-- Complement the quadword of slice `j` of the round key at `kp`. -/
def flip (j : Nat) : List Instr :=
  [.mov .r10 (.mem (at_ kp (8 * j))), .alu .xor .r10 (.imm 0xFFFFFFFF), .store (at_ kp (8 * j)) .r10]

/-- Add `{63}` to the round key at `kp`, on to the next. -/
def complement : List Instr :=
  flip 0 ++ flip 1 ++ flip 5 ++ flip 6 ++ [.alu .add kp (.imm 64), .alu .sub .rdi (.imm 1)]

/-- The round keys in slices in the scratch buffer (`r9`), from the schedule
at `rdi`, of `rsi` rounds (even); `{63}` added to all but the first. -/
def keys : Prog isa :=
  .seq (.block (setMasks ++ ([.mov .r10 (.reg .rdi), .mov kp (.reg .r9),
      .alu .add kp (.imm (BitVec.ofNat 32 keysOff)), .mov .rdi (.reg .rsi), .shift .shr .rdi 1] : List Instr)))
    (.seq (.loop (.block keyBody) .ne)
      (.seq (.block (keyLoad1 ++ (keySpread ++ toBs) ++ storeLow ++
          ([.mov kp (.reg .r9), .alu .add kp (.imm (BitVec.ofNat 32 (keysOff + 64))),
            .mov .rdi (.reg .rsi)] : List Instr)))
        (.loop (.block complement) .ne)))

/-! ## A batch -/

/-- The eight blocks of the buffer, halves in the registers. -/
def loadBuf : List Instr :=
  (List.range 4).flatMap fun k =>
    [ldx (q k) (bufSlot k), ldx .xmm8 (bufSlot (k + 4)), mv (q (k + 4)) (q k), unpckl (q k) .xmm8,
     unpckh (q (k + 4)) .xmm8]

/-- And back. -/
def storeBuf : List Instr :=
  (List.range 4).flatMap fun k =>
    [mv .xmm8 (q k), unpckl .xmm8 (q (k + 4)), unpckh (q k) (q (k + 4)), stx (bufSlot k) .xmm8,
     stx (bufSlot (k + 4)) (q k)]

def nextKey : Instr := .alu .add kp (.imm 64)
def prevKey : Instr := .alu .sub kp (.imm 64)

/-- The round from form 0 to form 1, whose round key is at `kp`. -/
def roundA : List Instr :=
  subBytes ++ mixColumns true ++ addRoundKey q .xmm8 .xmm9 ++ [nextKey]

/-- The round from form 1 to form 0. -/
def roundB : List Instr :=
  subBytes ++ sr2 p .xmm0 .xmm1 ++ mixColumns false ++ addRoundKey q .xmm8 .xmm9 ++ [nextKey]

/-- The state's registers, after the last SubBytes. -/
def moveBack : List Instr := (List.range 8).map fun j => mv (q j) (p j)

def lastB : List Instr :=
  subBytes ++ sr2 p .xmm0 .xmm1 ++ addRoundKey p .xmm0 .xmm1 ++ moveBack

/-- The number of pairs of rounds before the last, to `r10`. -/
def pairs : List Instr := [.mov .r10 (.reg .rsi), .shift .shr .r10 1, .alu .sub .r10 (.imm 1)]

/-- Encipher the buffer's eight blocks, in place. -/
def encrypt8 : Prog isa :=
  .seq (.block (loadBuf ++ toBs ++ pairs ++ ([.mov kp (.reg .r9), .alu .add kp (.imm (BitVec.ofNat 32 keysOff))] : List Instr) ++
      addRoundKey q .xmm8 .xmm9 ++ [nextKey]))
    (.seq (.loop (.block (roundA ++ roundB ++ ([.alu .sub .r10 (.imm 1)] : List Instr))) .ne)
      (.block (roundA ++ lastB ++ fromBs ++ storeBuf)))

/-- The inverse cipher's round from form 0 to form 1, and from 1 to 0. -/
def invRoundA : List Instr :=
  sr2 q .xmm8 .xmm9 ++ invSubBytes ++ addRoundKey p .xmm0 .xmm1 ++ invMixColumns true ++ [prevKey]

def invRoundB : List Instr :=
  invSubBytes ++ addRoundKey p .xmm0 .xmm1 ++ invMixColumns false ++ [prevKey]

def invLastB : List Instr := invSubBytes ++ addRoundKey p .xmm0 .xmm1 ++ moveBack

/-- Decipher the buffer's eight blocks, in place: the round keys from the last. -/
def decrypt8 : Prog isa :=
  .seq (.block (loadBuf ++ toBs ++ pairs ++ ([.mov kp (.reg .rsi), .shift .shl kp 6, .alu .add kp (.reg .r9),
        .alu .add kp (.imm (BitVec.ofNat 32 keysOff))] : List Instr) ++
      addRoundKey q .xmm8 .xmm9 ++ [prevKey]))
    (.seq (.loop (.block (invRoundA ++ invRoundB ++ ([.alu .sub .r10 (.imm 1)] : List Instr))) .ne)
      (.block (invRoundA ++ invLastB ++ fromBs ++ storeBuf)))

/-! ## Whole blocks

The data are at `rcx`, `r8` blocks; `rdi` is the number of blocks of the
batch. -/

/-- The blocks of this batch, at most eight, to `rdi` and `r10`; the buffer's
address to `rax`. -/
def batchSize : List Instr :=
  [.mov .rdi (.imm 8), .alu .cmp .r8 (.imm 8), .cmov .b .rdi (.reg .r8), .mov .r10 (.reg .rdi),
   .mov .rax (.reg .r9), .alu .add .rax (.imm (BitVec.ofNat 32 (16 * bufSlot 0)))]

/-- A block of the data to the buffer. -/
def copyIn : List Instr :=
  [.movdquLoad .xmm0 (at_ .r11 0), .movdquStore (at_ .rax 0) .xmm0, .alu .add .r11 (.imm 16),
   .alu .add .rax (.imm 16), .alu .sub .r10 (.imm 1)]

/-- A block of the buffer to the data. -/
def copyOut : List Instr :=
  [.movdquLoad .xmm0 (at_ .rax 0), .movdquStore (at_ .rcx 0) .xmm0, .alu .add .rcx (.imm 16),
   .alu .add .rax (.imm 16), .alu .sub .r10 (.imm 1)]

/-- Up to eight blocks of the data through `crypt8`, in place. -/
def blocksBatch (crypt8 : Prog isa) : Prog isa :=
  .seq (.block (batchSize ++ ([.mov .r11 (.reg .rcx)] : List Instr)))
    (.seq (.loop (.block copyIn) .ne)
      (.seq crypt8
        (.seq (.block batchSize)
          (.seq (.loop (.block copyOut) .ne) (.block [.alu .sub .r8 (.reg .rdi)])))))

/-- `vg_aes_encrypt_blocks(schedule = rdi, rounds = rsi, data = rdx, n = rcx,
scratch = r8)`, and `vg_aes_decrypt_blocks`. -/
def blocks (crypt8 : Prog isa) : Prog isa :=
  .seq (.block [.mov .r9 (.reg .r8), .mov .r8 (.reg .rcx), .mov .rcx (.reg .rdx), .alu .test .r8 (.reg .r8)])
    (.ite .e (.block []) (.seq keys (.loop (blocksBatch crypt8) .ne)))

/-! ## Counter mode -/

/-- Counter block `i` of the batch to the buffer: the block in `xmm0` with the
last word `eax + i`, big-endian. -/
def ctrBlock (i : Nat) : List Instr :=
  [stx (bufSlot i) .xmm0, .mov32 .r10 (.reg .rax), .alu32 .add .r10 (.imm (BitVec.ofNat 32 i)), .bswap32 .r10,
   .store32 (at_ .r9 (16 * bufSlot i + 12)) .r10]

/-- The eight counter blocks, from the counter block at `rdx`. -/
def ctrBlocks : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdx 0), .mov32 .rax (.mem (at_ .rdx 12)), .bswap32 .rax] ++
    (List.range 8).flatMap ctrBlock

/-- A block of the keystream, in the buffer, XORed into one of the data, to `r11`. -/
def xorBlock : List Instr :=
  [.movdquLoad .xmm0 (at_ .rax 0), .movdquLoad .xmm1 (at_ .rcx 0), px .xmm0 .xmm1,
   .movdquStore (at_ .r11 0) .xmm0, .alu .add .rax (.imm 16), .alu .add .rcx (.imm 16), .alu .add .r11 (.imm 16),
   .alu .sub .r10 (.imm 1)]

/-- The counter moved on by the batch's blocks. -/
def ctrNext : List Instr :=
  [.mov32 .rax (.mem (at_ .rdx 12)), .bswap32 .rax, .alu32 .add .rax (.reg .rdi), .bswap32 .rax,
   .store32 (at_ .rdx 12) .rax, .alu .sub .r8 (.reg .rdi)]

/-- Up to eight blocks in counter mode. -/
def ctrBatch : Prog isa :=
  .seq (.block ctrBlocks)
    (.seq encrypt8
      (.seq (.block batchSize) (.seq (.loop (.block xorBlock) .ne) (.block ctrNext))))

/-- Counter mode, from the round keys in slices. -/
def ctrLoop : Prog isa := .loop ctrBatch .ne

/-- `vg_aes_ctr32(schedule = rdi, rounds = rsi, counter = rdx, data = rcx, n = r8,
scratch = r9)`, and (`to`) `vg_aes_ctr32_to`, whose output is at `r11`. -/
def ctr32G (to : Bool) : Prog isa :=
  .seq (.block ((if to then [] else [.mov .r11 (.reg .rcx)]) ++ ([.alu .test .r8 (.reg .r8)] : List Instr)))
    (.ite .e (.block []) (.seq keys ctrLoop))

end VG.Impl.Aes.X86_64.Sse
