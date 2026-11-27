module

public import VerifiedGarbage.Impl.Modes.X86.Wide
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal
public import VerifiedGarbage.Impl.Modes.X86.Ecb
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Spec.Seed

/-!
# SEED on x86 (32-bit), bitsliced in XMM registers: sixteen blocks at a time

The modes' core (`core d`, `Impl/Modes/X86/Seq.lean`) of the baseline's SEED,
in SSE2. F joins its three `G` with additions (RFC 4269 §2.1), so the state's
words stay words: each of the four words of the sixteen blocks is four slots
of the scratch buffer (16 bytes each, at `sb`), doubleword `l` of slot `q`
block `4 q + l`'s. `G` (`g`) of sixteen words, in the slots `gS` and up, is
bitsliced inside:

1. `gIn` transposes the 4 × 4 bits of each half byte of the four registers,
   so that bit `4 n + r` of the register `k` is bit `k` of the half byte `n`
   of the register `r`'s; the slots `0` to `7` are then eight planes, of
   bytes' low halves and, shifted, of their high halves: in a byte of plane
   `j`, the low four bits are bit `j` of that byte of the four registers, and
   the others are left whatever they are;
2. `sboxCode` runs both S-boxes' circuit on every bit of the planes: they
   share the inversion, and the linear layer after it takes the difference
   of the two under a mask of the bytes of `S1`'s place in a word. Without its
   constants: the planes are of `S0(x) ⊕ 0xa9` and `S1(x) ⊕ 0x38`;
3. `gOut` transposes back, and mixes each word's S-boxes' outputs, XORing
   the constant that `0xa9` and `0x38` add to `G`.

`g` is an internal function, which a round calls three times and the key
expansion twice. A round key is in every doubleword of its slot (`prepare`).

`crypt` calls the block function, an internal function too, which the modes'
loops for groups of sixteen, eight, four and two blocks and for one
(`levels`) share: it costs the same for any number of them. Its constants
are in the static `table`, whose address `prepare` keeps in a slot. Every
address depends only on the loops' counts and the pointers.
-/

@[expose] public section

namespace VG.Impl.Seed.X86.Sse

open VG.X86
open VG.Impl.Modes.X86 (sb at_ argOp Core)
open VG.Spec.Seed (Direction)

/-! ## The slots, and the table -/

/-- The slots of 16 bytes: the S-box's planes (0–7) and spills (9–28), the
table's address (`tblSlot`), `G`'s words (`gS`), F's values `A`, `C` and `D`
(`aS`, `cS` and `dS`), the four words of the state (`arr`), the blocks
(`bufS`) and the round keys (`keyS`). -/
def tblSlot : Nat := 30
def gS : Nat := 32
def aS : Nat := 36
def cS : Nat := 40
def dS : Nat := 44
def arr (k : Nat) : Nat := 48 + 4 * k
def bufS : Nat := 64
def keyS : Nat := 80

def tableName : String := "VG_SEED_SSE2"

/-- The masks of the transposes (bytes 0 to 47: every second bit, pair of
bits and half byte) and of the low byte of every 16-bit lane (48), the masks
of `G`'s mixing, of each rotation of the word (64 to 127), and its constant
(128). -/
def table : List (BitVec 64) := [
  0x5555555555555555, 0x5555555555555555,
  0x3333333333333333, 0x3333333333333333,
  0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f,
  0x00ff00ff00ff00ff, 0x00ff00ff00ff00ff,
  0xcffccffccffccffc, 0xcffccffccffccffc,
  0x3ff33ff33ff33ff3, 0x3ff33ff33ff33ff3,
  0xfccffccffccffccf, 0xfccffccffccffccf,
  0xf33ff33ff33ff33f, 0xf33ff33ff33ff33f,
  0xb829b829b829b829, 0xb829b829b829b829]

/-- The mask of the S-box. -/
def oM : Nat := 48

/-- The table, and the round keys. -/
def tbr : Reg := .ebx
def kr : Reg := .esi

/-- The table's 16 bytes at `off`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table
def x (op : XBinOp) (a b : XReg) : Instr := .xop (.bin op a b)
def sh (op : XShiftOp) (a : XReg) (n : Nat) : Instr := .xop (.shift op a n)
def ld (d : XReg) (b : Reg) (off : Nat) : Instr := .movdquLoad d (at_ b off)
def stx (b : Reg) (off : Nat) (r : XReg) : Instr := .movdquStore (at_ b off) r

/-- Slot `k`. -/
def ldS (d : XReg) (k : Nat) : Instr := ld d sb (16 * k)
def stS (k : Nat) (r : XReg) : Instr := stx sb (16 * k) r
def mv (a b : XReg) : Instr := x .movdqa a b

/-- The halves of every doubleword of `b` swapped, to `a`. -/
def sw (a b : XReg) : List Instr := [.xop (.pshuflw a b 0xb1), .xop (.pshufhw a a 0xb1)]

/-! ## G -/

/-- The S-boxes of the planes in slots 0–7, XORed with their constants, in
the same slots. -/
def sboxCode : List Instr := [
  ldS .xmm7 1, ldS .xmm6 2, x .pxor .xmm6 .xmm7, ldS .xmm5 2, ldS .xmm4 6, x .pxor .xmm4 .xmm5, ldS .xmm3 0,
  x .pxor .xmm3 .xmm4, ldS .xmm2 3, x .pxor .xmm2 .xmm3, ldS .xmm3 0, x .pxor .xmm3 .xmm7, ldS .xmm1 0,
  ldS .xmm0 4, x .pxor .xmm0 .xmm1, ldS .xmm1 4, x .pxor .xmm1 .xmm4, stS 9 .xmm2, x .movdqa .xmm2 .xmm7,
  x .pxor .xmm2 .xmm1, stS 10 .xmm3, ldS .xmm3 6, x .pxor .xmm3 .xmm0, x .pxor .xmm5 .xmm0,
  x .movdqa .xmm0 .xmm2, x .pand .xmm0 .xmm6, stS 11 .xmm3, ldS .xmm3 7, x .pxor .xmm3 .xmm5, stS 12 .xmm0,
  ldS .xmm0 5, stS 13 .xmm6, ldS .xmm6 7, x .pxor .xmm6 .xmm0, x .pxor .xmm1 .xmm6, stS 14 .xmm3, ldS .xmm3 3,
  x .pxor .xmm3 .xmm6, x .pxor .xmm5 .xmm3, x .pxor .xmm6 .xmm7, x .pxor .xmm4 .xmm3, stS 15 .xmm6,
  x .movdqa .xmm6 .xmm4, x .pand .xmm6 .xmm5, stS 16 .xmm5, x .movdqa .xmm5 .xmm1, x .pand .xmm5 .xmm3,
  stS 17 .xmm5, ldS .xmm5 4, x .pxor .xmm5 .xmm3, x .pxor .xmm7 .xmm5, stS 18 .xmm3, ldS .xmm3 10,
  x .pxor .xmm3 .xmm5, x .movdqa .xmm5 .xmm7, x .pand .xmm5 .xmm3, stS 19 .xmm3, ldS .xmm3 10,
  x .pxor .xmm3 .xmm1, stS 20 .xmm7, ldS .xmm7 10, x .pxor .xmm7 .xmm4, stS 21 .xmm4, ldS .xmm4 7,
  x .pand .xmm4 .xmm3, stS 22 .xmm3, ldS .xmm3 3, x .pxor .xmm3 .xmm0, stS 23 .xmm1, ldS .xmm1 10,
  x .pand .xmm1 .xmm3, ldS .xmm0 10, x .pxor .xmm0 .xmm3, x .pxor .xmm1 .xmm6, stS 24 .xmm3, ldS .xmm3 4,
  x .pxor .xmm3 .xmm0, stS 25 .xmm0, ldS .xmm0 9, x .pand .xmm0 .xmm3, x .pxor .xmm5 .xmm0,
  x .pxor .xmm5 .xmm1, x .pxor .xmm4 .xmm0, ldS .xmm0 0, x .pxor .xmm0 .xmm5, ldS .xmm5 5, x .pxor .xmm5 .xmm2,
  stS 26 .xmm3, ldS .xmm3 14, x .pand .xmm3 .xmm7, x .pxor .xmm3 .xmm6, x .pxor .xmm4 .xmm3,
  x .pxor .xmm4 .xmm5, x .movdqa .xmm5 .xmm4, x .pxor .xmm5 .xmm0, ldS .xmm6 18, stS 27 .xmm7, ldS .xmm7 13,
  x .pxor .xmm7 .xmm6, ldS .xmm6 15, x .pand .xmm6 .xmm7, stS 28 .xmm7, ldS .xmm7 12, x .pxor .xmm7 .xmm6,
  x .pxor .xmm7 .xmm1, ldS .xmm1 17, x .pxor .xmm1 .xmm6, x .pxor .xmm1 .xmm3, ldS .xmm3 25,
  x .pxor .xmm3 .xmm7, ldS .xmm7 11, x .pxor .xmm7 .xmm1, x .movdqa .xmm1 .xmm7, x .pxor .xmm1 .xmm3,
  x .pand .xmm7 .xmm4, x .movdqa .xmm6 .xmm3, x .pxor .xmm6 .xmm7, x .pand .xmm6 .xmm5, x .pxor .xmm7 .xmm0,
  x .pxor .xmm6 .xmm0, x .pxor .xmm4 .xmm6, ldS .xmm5 13, x .pand .xmm5 .xmm6, x .pand .xmm2 .xmm6,
  stS 13 .xmm5, x .movdqa .xmm5 .xmm7, x .pxor .xmm5 .xmm6, x .pand .xmm0 .xmm5, x .pxor .xmm4 .xmm0,
  x .pxor .xmm0 .xmm7, ldS .xmm5 23, x .pand .xmm5 .xmm4, x .pand .xmm7 .xmm1, x .pxor .xmm7 .xmm3,
  x .pand .xmm0 .xmm7, x .pxor .xmm1 .xmm0, ldS .xmm0 20, x .pand .xmm0 .xmm7, x .pxor .xmm0 .xmm2,
  x .movdqa .xmm3 .xmm1, x .pxor .xmm3 .xmm4, stS 20 .xmm0, ldS .xmm0 10, x .pand .xmm0 .xmm3,
  x .pxor .xmm2 .xmm0, x .movdqa .xmm0 .xmm5, x .pxor .xmm0 .xmm2, stS 10 .xmm2, ldS .xmm2 18,
  x .pand .xmm2 .xmm4, x .pxor .xmm4 .xmm6, stS 18 .xmm5, ldS .xmm5 28, x .pand .xmm5 .xmm4, stS 28 .xmm5,
  ldS .xmm5 15, x .pand .xmm5 .xmm4, x .pxor .xmm6 .xmm7, ldS .xmm4 16, x .pand .xmm4 .xmm6, stS 16 .xmm5,
  ldS .xmm5 21, x .pand .xmm5 .xmm6, x .pxor .xmm0 .xmm5, x .pxor .xmm6 .xmm3, stS 21 .xmm0, ldS .xmm0 24,
  x .pand .xmm0 .xmm3, ldS .xmm3 27, x .pand .xmm3 .xmm6, x .pxor .xmm5 .xmm3, stS 27 .xmm5, ldS .xmm5 14,
  x .pand .xmm5 .xmm6, x .movdqa .xmm6 .xmm4, x .pxor .xmm6 .xmm5, x .pxor .xmm5 .xmm0, x .pxor .xmm4 .xmm0,
  x .pxor .xmm3 .xmm4, ldS .xmm0 22, x .pand .xmm0 .xmm1, stS 22 .xmm3, ldS .xmm3 7, x .pand .xmm3 .xmm1,
  x .pxor .xmm1 .xmm7, stS 14 .xmm0, ldS .xmm0 19, x .pand .xmm0 .xmm7, ldS .xmm7 9, x .pand .xmm7 .xmm1,
  stS 9 .xmm7, ldS .xmm7 26, x .pand .xmm7 .xmm1, x .movdqa .xmm1 .xmm7, x .pxor .xmm1 .xmm3,
  x .pxor .xmm3 .xmm0, x .pxor .xmm7 .xmm0, x .pxor .xmm4 .xmm7, x .pxor .xmm3 .xmm5, x .movdqa .xmm0 .xmm2,
  x .pxor .xmm0 .xmm5, x .pxor .xmm2 .xmm7, stS 26 .xmm7, ldS .xmm7 28, x .pxor .xmm7 .xmm5,
  x .movdqa .xmm5 .xmm7, x .pxor .xmm5 .xmm2, x .pxor .xmm7 .xmm1, x .pxor .xmm2 .xmm6, x .pxor .xmm1 .xmm6,
  ldS .xmm6 9, x .pxor .xmm6 .xmm1, stS 19 .xmm0, ldS .xmm0 21, x .pxor .xmm0 .xmm6, ldS .xmm6 14,
  x .pxor .xmm6 .xmm0, tb .xmm0 oM, x .pand .xmm0 .xmm6, ldS .xmm6 14, stS 21 .xmm2, ldS .xmm2 20,
  x .pxor .xmm2 .xmm6, ldS .xmm6 9, stS 14 .xmm1, ldS .xmm1 20, x .pxor .xmm1 .xmm6, x .pxor .xmm0 .xmm4,
  ldS .xmm6 18, x .pxor .xmm6 .xmm2, x .pxor .xmm4 .xmm6, stS 9 .xmm0, tb .xmm0 oM, x .pand .xmm0 .xmm4,
  x .pxor .xmm0 .xmm6, x .movdqa .xmm4 .xmm6, x .pxor .xmm4 .xmm3, stS 20 .xmm0, tb .xmm0 oM,
  x .pand .xmm0 .xmm4, x .pxor .xmm6 .xmm5, x .movdqa .xmm4 .xmm5, x .pxor .xmm4 .xmm1, stS 24 .xmm1,
  ldS .xmm1 16, x .pxor .xmm1 .xmm4, tb .xmm4 oM, x .pand .xmm4 .xmm1, ldS .xmm1 16, stS 15 .xmm6,
  ldS .xmm6 27, x .pxor .xmm6 .xmm1, x .pxor .xmm5 .xmm6, ldS .xmm1 18, x .pxor .xmm1 .xmm5, tb .xmm5 oM,
  x .pand .xmm5 .xmm1, x .pxor .xmm2 .xmm6, x .pxor .xmm6 .xmm7, x .pxor .xmm3 .xmm2, x .pxor .xmm3 .xmm4,
  ldS .xmm4 13, ldS .xmm1 18, x .pxor .xmm1 .xmm4, x .pxor .xmm6 .xmm1, x .pxor .xmm6 .xmm0, ldS .xmm0 28,
  x .pxor .xmm0 .xmm1, x .pxor .xmm4 .xmm2, ldS .xmm1 14, x .pxor .xmm1 .xmm2, tb .xmm2 oM,
  x .pand .xmm2 .xmm1, ldS .xmm1 15, x .pxor .xmm1 .xmm2, x .pxor .xmm7 .xmm4, tb .xmm2 oM,
  x .pand .xmm2 .xmm7, ldS .xmm7 21, x .pxor .xmm7 .xmm4, stS 21 .xmm6, tb .xmm6 oM, x .pand .xmm6 .xmm7,
  ldS .xmm7 19, x .pxor .xmm7 .xmm4, x .pxor .xmm7 .xmm5, ldS .xmm5 24, x .pxor .xmm5 .xmm0, ldS .xmm4 26,
  x .pxor .xmm4 .xmm5, ldS .xmm5 27, x .pxor .xmm5 .xmm4, x .pxor .xmm5 .xmm2, ldS .xmm2 22,
  x .pxor .xmm2 .xmm0, ldS .xmm0 10, x .pxor .xmm0 .xmm2, x .pxor .xmm0 .xmm6, stS 1 .xmm1, stS 3 .xmm3,
  stS 5 .xmm0, stS 6 .xmm7, stS 7 .xmm5, ldS .xmm0 21, stS 0 .xmm0, ldS .xmm0 9, stS 2 .xmm0, ldS .xmm0 20,
  stS 4 .xmm0]

/-- The register of the four words of `G`, of a state's word, or the four
words of four blocks, `k < 4`. -/
def w : Nat → XReg
  | 0 => .xmm0
  | 1 => .xmm1
  | 2 => .xmm2
  | _ => .xmm3

/-- The bits of `a` that the mask in `xmm6` shifted left by `n` has, swapped
with those of `b` that the mask has. -/
def swapm (n : Nat) (a b : XReg) : List Instr :=
  [mv .xmm4 a, sh .psrlq .xmm4 n, x .pxor .xmm4 b, x .pand .xmm4 .xmm6, x .pxor b .xmm4, sh .psllq .xmm4 n, x .pxor a .xmm4]

def st1 : List Instr := tb .xmm6 0 :: (swapm 1 .xmm0 .xmm1 ++ swapm 1 .xmm2 .xmm3)
def st2 : List Instr := tb .xmm6 16 :: (swapm 2 .xmm0 .xmm2 ++ swapm 2 .xmm1 .xmm3)

/-- `G`'s words to the planes. -/
def gIn : List Instr :=
  (List.range 4).map (fun k => ldS (w k) (gS + k)) ++ st1 ++ st2 ++
    (List.range 4).flatMap fun k => [stS k (w k), sh .psrld (w k) 4, stS (k + 4) (w k)]

/-- The mixing of the S-boxes' outputs of the words in `w k`, to slot
`gS + k`. -/
def mix (k : Nat) : List Instr :=
  [mv .xmm4 (w k), sh .psrld .xmm4 8, mv .xmm5 (w k), sh .pslld .xmm5 24, x .pxor .xmm4 .xmm5,
   mv .xmm5 (w k), tb .xmm6 96, x .pand .xmm5 .xmm6, tb .xmm6 64, x .pand (w k) .xmm6,
   mv .xmm7 .xmm4, tb .xmm6 80, x .pand .xmm4 .xmm6, tb .xmm6 112, x .pand .xmm7 .xmm6,
   x .pxor (w k) .xmm4, x .pxor .xmm5 .xmm7] ++ sw .xmm5 .xmm5 ++
  [x .pxor (w k) .xmm5, tb .xmm6 128, x .pxor (w k) .xmm6, stS (gS + k) (w k)]

/-- The planes of the S-boxes' outputs to `G`'s words. -/
def gOut : List Instr :=
  [tb .xmm6 32] ++ (List.range 4).flatMap (fun k =>
    [ldS (w k) k, x .pand (w k) .xmm6, ldS .xmm4 (k + 4), x .pand .xmm4 .xmm6, sh .pslld .xmm4 4, x .pxor (w k) .xmm4]) ++
  st2 ++ st1 ++ (List.range 4).flatMap mix

/-- `G` of the sixteen words in the slots `gS` and up, in place. -/
def g : List Instr := gIn ++ (sboxCode ++ gOut)

def gCall : Prog isa := .call "vg_seed_g16_sse2" (.block g)

/-! ## A round -/

/-- `f` of each of a word's four slots. -/
def lanes (f : Nat → List Instr) : List Instr := (List.range 4).flatMap f

/-- A round's start: with `R0` and `R1` in the slots `r` and `r + 4` and up,
`A = R0 ⊕ K0` to `aS`, and `A ⊕ R1 ⊕ K1` to `gS`. -/
def step1 (r ko : Nat) : List Instr := [ld .xmm6 kr ko, ld .xmm7 kr (ko + 16)] ++ lanes fun k =>
  [ldS .xmm0 (r + k), x .pxor .xmm0 .xmm6, stS (aS + k) .xmm0, ldS .xmm1 (r + 4 + k), x .pxor .xmm0 .xmm1,
   x .pxor .xmm0 .xmm7, stS (gS + k) .xmm0]

/-- `C`, in `gS`, to `cS`, and `C + A` to `gS`. -/
def step2 : List Instr := lanes fun k =>
  [ldS .xmm0 (gS + k), stS (cS + k) .xmm0, ldS .xmm1 (aS + k), x .paddd .xmm0 .xmm1, stS (gS + k) .xmm0]

/-- `D`, in `gS`, to `dS`, and `D + C` to `gS`. -/
def step3 : List Instr := lanes fun k =>
  [ldS .xmm0 (gS + k), stS (dS + k) .xmm0, ldS .xmm1 (cS + k), x .paddd .xmm0 .xmm1, stS (gS + k) .xmm0]

/-- `E`, in `gS`, and `E + D` into the left half, in the slots `l + 4` and
`l` and up. -/
def step4 (l : Nat) : List Instr := lanes fun k =>
  [ldS .xmm0 (gS + k), ldS .xmm1 (l + 4 + k), x .pxor .xmm1 .xmm0, stS (l + 4 + k) .xmm1, ldS .xmm1 (dS + k),
   x .paddd .xmm0 .xmm1, ldS .xmm1 (l + k), x .pxor .xmm0 .xmm1, stS (l + k) .xmm0]

/-- A round of the right half at `r`, into the left at `l`, with the round
keys at byte `ko` from `kr`. -/
def round (l r ko : Nat) : Prog isa :=
  .seq (.block (step1 r ko)) (.seq gCall (.seq (.block step2) (.seq gCall (.seq (.block step3) (.seq gCall
    (.block (step4 l)))))))

/-- Two rounds, on by their keys, and the count of the pairs. -/
def turn : Prog isa :=
  .seq (round (arr 0) (arr 2) 0) (.seq (round (arr 2) (arr 0) 32)
    (.block [.alu .add kr (.imm 64), .alu .sub .ecx (.imm 1)]))

/-! ## The blocks -/

/-- The bytes of every doubleword of `a` reversed (with the mask of the low
bytes of the 16-bit lanes in `xmm6`). -/
def rev (a : XReg) : List Instr :=
  sw a a ++ [mv .xmm7 a, sh .psrld .xmm7 8, x .pand .xmm7 .xmm6, x .pand a .xmm6, sh .pslld a 8, x .pxor a .xmm7]

/-- The 4 × 4 doublewords of `w 0` to `w 3` transposed. -/
def tr4 : List Instr :=
  [mv .xmm4 .xmm0, x .punpckldq .xmm0 .xmm1, x .punpckhdq .xmm4 .xmm1, mv .xmm5 .xmm2, x .punpckldq .xmm2 .xmm3,
   x .punpckhdq .xmm5 .xmm3, mv .xmm1 .xmm0, x .punpcklqdq .xmm0 .xmm2, x .punpckhqdq .xmm1 .xmm2, mv .xmm2 .xmm4,
   x .punpcklqdq .xmm2 .xmm5, mv .xmm3 .xmm4, x .punpckhqdq .xmm3 .xmm5]

/-- Blocks `4 q` to `4 q + 3` to slot `q` of the four words. -/
def blockIn (q : Nat) : List Instr :=
  (List.range 4).flatMap (fun k => ldS (w k) (bufS + 4 * q + k) :: rev (w k)) ++ tr4 ++
  (List.range 4).map (fun k => stS (arr k + q) (w k))

/-- Slot `q` of the four words, the halves swapped, to blocks `4 q` to
`4 q + 3`. -/
def blockOut (q : Nat) : List Instr :=
  (List.range 4).map (fun k => ldS (w k) (arr ((k + 2) % 4) + q)) ++ tr4 ++
  (List.range 4).flatMap (fun k => rev (w k) ++ [stS (bufS + 4 * q + k) (w k)])

def blocksIn : List Instr := tb .xmm6 48 :: lanes blockIn
def blocksOut : List Instr := tb .xmm6 48 :: lanes blockOut

/-! ## The block function -/

/-- The block function on the sixteen blocks of the buffer, with eight in
`ecx`, the table in `tbr` and the round keys in `kr`. -/
def cryptFn : Prog isa := .seq (.block blocksIn) (.seq (.loop turn .ne) (.block blocksOut))

/-- The table, the pairs of rounds and the round keys. -/
def cryptSetup : List Instr :=
  [.mov tbr (.mem (at_ sb 480)), .mov .ecx (.imm 8), .mov kr (.reg sb), .alu .add kr (.imm 1280)]

/-- The core's code: a call of the block function. -/
def crypt : Prog isa := .seq (.block cryptSetup) (.call "vg_seed_crypt16_sse2" cryptFn)

/-! ## The round keys -/

/-- The first round keys' place in the schedule: the last two for decryption. -/
def keyAt : Direction → Nat
  | .encrypt => 0
  | .decrypt => 120

/-- On to the next round's keys. -/
def keyNext : Direction → Instr
  | .encrypt => .alu .add .eax (.imm 8)
  | .decrypt => .alu .sub .eax (.imm 8)

/-- A round's keys, at `eax`, to every doubleword of the next two slots. -/
def prepOne : List Instr :=
  [.movqLoad .xmm0 (at_ .eax 0), .xop (.pshufd .xmm1 .xmm0 0x00), stx kr 0 .xmm1, .xop (.pshufd .xmm1 .xmm0 0x55),
   stx kr 16 .xmm1]

/-- A constant of the table, at `eax`, to a register that nothing reads: the
other loads of the table are in the internal functions, and a function's
table is one that its own code reads. -/
def ownTable : Instr := .movdquTbl .xmm0 (at_ .eax 0) tableName table

/-- The table's address (in `eax`) to its slot, the schedule from the stack
arguments, and the count of the rounds. -/
def prepHead (d : Direction) : List Instr :=
  [.store (at_ sb 480) .eax, ownTable, .mov .eax (.mem (argOp 0)), .alu .add .eax (.imm (BitVec.ofNat 32 (keyAt d))),
   .mov kr (.reg sb), .alu .add kr (.imm 1280), .mov .ecx (.imm 16)]

/-- The round keys of the schedule (`argOp 0`), in the order of the
direction, and the table's address, in their slots. -/
def prepare (d : Direction) : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.seq (.block (prepHead d)) (.loop (.block (prepOne ++ [keyNext d, .alu .add kr (.imm 32), .alu .sub .ecx (.imm 1)])) .ne))

/-! ## The core, and the modes -/

/-- The core's slots, in doublewords. -/
def slots : Nat := 448

/-- SEED's core of sixteen blocks for the direction `d`. -/
def core (d : Direction) : Core :=
  { prepare := prepare d, crypt := crypt, slots := slots, total := slots + 10, buf := 256, G := 16, bw := 4,
    stack := 8, ka := 1 }

/-- The sizes of the groups of blocks a wide mode takes in turn, before the
blocks left one at a time. -/
def levels : List Nat := [16, 8, 4, 2]

/-- `vg_seed_ecb_encrypt` or `vg_seed_ecb_decrypt`, with its scratch buffer
as the fourth argument. -/
def ecb (d : Direction) : Prog isa := (core d).ecbLevels levels

/-- `vg_seed_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa :=
  (core .decrypt).seqLevels (Modes.Mode.cbcDecWide 4) levels (Modes.Mode.cbcDecChained 4)

/-- `vg_seed_cfb128_decrypt`, with its scratch buffer as the fifth argument. -/
def cfbDecrypt : Prog isa :=
  (core .encrypt).seqLevels (Modes.Mode.cfbDecWide 4) levels (Modes.Mode.cfbDecEarly 4)

/-- `vg_seed_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (core .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_seed_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := (core .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_seed_cfb128_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := (core .encrypt).seq (Modes.Mode.cfbEnc 4)


/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (core .encrypt).seqFinal (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (core .encrypt).seqFinal (Modes.Mode.cfbDec 4)

/-- `vg_seed_ofb_final`. -/
def ofbFinal : Prog isa := (core .encrypt).seqFinal (Modes.Mode.ofb 4)

end VG.Impl.Seed.X86.Sse
