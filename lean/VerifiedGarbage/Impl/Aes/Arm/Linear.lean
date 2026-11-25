module

public import VerifiedGarbage.Impl.Aes.Arm.Sbox

/-!
# The linear layers of bitsliced AES on ARMv7

Two blocks at a time: the byte of row `r` and column `c` of block `b` is at
bit `b + 2 c + 8 r` of the slices, so that a row is a byte of a slice and the
next row's a rotation of the word by 8 bits, which an operand has for
nothing.

**ShiftRows is not done.** In form `f` of the state (`f < 4`, form 0 the plain
one) the byte of row `r` and column `c` is at column `c + f r`. A state whose
bytes a round leaves where they were is the state after ShiftRows one form
further, and the other layers allow for it: MixColumns of form `f` takes the
next row's byte `f` columns further, and the round keys are stored in their
rounds' forms. The inverse cipher goes the other way round the forms.

`ortho` is the transpose of the 8×8 bit matrices that the registers `q 0 … q
7` hold a byte each: bit `j` of byte `i` of `q k` becomes bit `k` of byte `i`
of `q j`. It exchanges the three index bits of the bits within a byte with
those of the registers' numbers, each by exchanges between four pairs of
registers. On two blocks, word `c` of block `b` in `q (2 c + b)`, that gives
the slices in form 0, and back.
-/

@[expose] public section

namespace VG.Impl.Aes.Arm

open VG.Arm

/-! ## Blocks and slices -/

/-- Exchange the bits of `lo` `n` places above those of the mask in `t1` with
the bits of `hi` at the mask's. -/
def swapMove (lo hi : Reg) (n : Nat) : List Instr :=
  [.dp .eor t0 hi (lsrOp lo n), andR t0 t0 t1, eorR hi hi t0, .dp .eor lo lo (rorOp t0 (32 - n))]

/-- The positions whose index bit `i` is 0. -/
def idxMask : Nat → BitVec 32
  | 0 => 0x55555555 | 1 => 0x33333333 | _ => 0x0F0F0F0F

/-- Exchange bit `i` of the positions with bit `i` of the register's number. -/
def exchange (i : Nat) : List Instr :=
  imm32 t1 (idxMask i) ++ ((List.range 8).filter fun k => k / 2 ^ i % 2 == 0).flatMap fun k =>
    swapMove (q k) (q (k + 2 ^ i)) (2 ^ i)

/-- The transpose of the 8×8 bit matrices. -/
def ortho : List Instr := exchange 2 ++ exchange 1 ++ exchange 0

/-- The exchange of the odd rows' columns `c` and `c + 2` on blocks' words:
from form 0 to form 2, and back. -/
def sr2Words : List Instr :=
  imm32 t1 0xFF00FF00 ++ ([0, 1, 2, 3] : List Nat).flatMap fun k =>
    [eorR t0 (q k) (q (k + 4)), andR t0 t0 t1, eorR (q k) (q k) t0, eorR (q (k + 4)) (q (k + 4)) t0]

/-! ## MixColumns -/

/-- `t` := `a` with the bits of its bytes rotated right by `s` places, all
rotated left by `s`; `m` holds the mask of the bytes' `s` lowest bits. -/
def rotBytes (t a m : Reg) : List Instr :=
  [andR t a m, .dp .eor t t (rorOp t 24), eorR t t a]

/-- The mask of `rotBytes`. -/
def byteMask : Nat → BitVec 32
  | 2 => 0x03030303 | 4 => 0x0F0F0F0F | _ => 0x3F3F3F3F

/-- The mask of rotations by two columns, in `t0`. -/
def mask2 (f : Nat) : List Instr := if f = 0 then [] else imm32 t0 (byteMask 4)

/-- The mask of rotations by `f` columns, from that, in `kp`, for odd `f`. -/
def maskF (f : Nat) : List Instr :=
  if f = 1 then [.dp .and kp t0 (rorOp t0 2)] else if f = 3 then [.dp .orr kp t0 (rorOp t0 30)] else []

/-- With `a` the slice, `next` its next row's bytes (made in `t1`) and
`b = a ⊕ next`: `o` := `o'` with `next` and `b`'s bytes two rows on added, and
`b` in `a`'s register. -/
def mcStep (f : Nat) (a o o' : Reg) : List Instr :=
  if f = 0 then
    [.dp .eor o o' (rorOp a 8), .dp .eor a a (rorOp a 8), .dp .eor o o (rorOp a 16)]
  else
    rotBytes t1 a (if f = 2 then t0 else kp) ++
    [.dp .eor o o' (rorOp t1 (8 + 2 * f)), .dp .eor a a (rorOp t1 (8 + 2 * f))] ++
    if f = 2 then [.dp .eor o o (rorOp a 16)]
    else rotBytes t1 a t0 ++ [.dp .eor o o (rorOp t1 20)]

/-- The same for slice 7, with no `o'`, to `t2`. -/
def mcTop (f : Nat) : List Instr :=
  if f = 0 then [.mov t2 (rorOp (p 7) 8), eorR (p 7) (p 7) t2, .dp .eor t2 t2 (rorOp (p 7) 16)]
  else
    rotBytes t1 (p 7) (if f = 2 then t0 else kp) ++
    [.mov t2 (rorOp t1 (8 + 2 * f)), eorR (p 7) (p 7) t2] ++
    if f = 2 then [.dp .eor t2 t2 (rorOp (p 7) 16)]
    else rotBytes t1 (p 7) t0 ++ [.dp .eor t2 t2 (rorOp t1 20)]

/-- MixColumns of form `f`, from `p j` to `q j`, but for `mask2`: with
`b = a ⊕ next(a)`, it is `2 b ⊕ next(a) ⊕ b`'s bytes two rows on. Slice 7
first, whose `b` the reduction adds to slices 0, 1, 3 and 4; slice `j`'s sum
starts from `b` of the slice below, in whose register it is made
(`q j = p (j - 1)`). -/
def mixCore (f : Nat) : List Instr :=
  maskF f ++ mcTop f ++ mcStep f (p 0) (q 0) (p 7) ++
  (List.range 6).flatMap (fun i => mcStep f (p (i + 1)) (q (i + 1)) (p i) ++
    if i = 0 ∨ i = 2 ∨ i = 3 then [eorR (q (i + 1)) (q (i + 1)) (p 7)] else []) ++
  ([eorR (q 7) (q 7) t2] : List Instr)

def mixColumns (f : Nat) : List Instr := mask2 f ++ mixCore f

/-! ## InvMixColumns -/

/-- `d` := `a` with its bytes two rows on added, in form `f`. -/
def invD (f : Nat) (d a : Reg) : List Instr :=
  if f % 2 = 0 then [.dp .eor d a (rorOp a 16)]
  else rotBytes d a t0 ++ [.dp .eor d a (rorOp d 20)]

/-- `d` := `d` with the same added. -/
def invAdd (f : Nat) (d a : Reg) : List Instr :=
  if f % 2 = 0 then [eorR d d a, .dp .eor d d (rorOp a 16)]
  else rotBytes t1 a t0 ++ [eorR d d a, .dp .eor d d (rorOp t1 20)]

/-- The state `a` plus `4 (a ⊕ a two rows on)`, whose MixColumns is
InvMixColumns of `a`; on `p j`, with slices 7 and 6 of that sum of two in
`q 0` and `kp`. -/
def preInv (f : Nat) : List Instr :=
  invD f (q 0) (p 7) ++ invD f kp (p 6) ++
  invAdd f (p 7) (p 5) ++ invAdd f (p 6) (p 4) ++
  invAdd f (p 5) (p 3) ++ ([eorR (p 5) (p 5) (q 0), eorR t2 (q 0) kp] : List Instr) ++
  invAdd f (p 4) (p 2) ++ ([eorR (p 4) (p 4) t2] : List Instr) ++
  invAdd f (p 3) (p 1) ++ ([eorR (p 3) (p 3) kp] : List Instr) ++
  invAdd f (p 2) (p 0) ++ ([eorR (p 2) (p 2) (q 0), eorR (p 1) (p 1) t2, eorR (p 0) (p 0) kp] : List Instr)

/-- InvMixColumns of form `f`, from `p j` to `q j`. -/
def invMixColumns (f : Nat) : List Instr := mask2 f ++ preInv f ++ mixCore f

end VG.Impl.Aes.Arm
