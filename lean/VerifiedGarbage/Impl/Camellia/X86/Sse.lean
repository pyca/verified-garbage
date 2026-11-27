module

public import VerifiedGarbage.Impl.Modes.X86.Wide
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal
public import VerifiedGarbage.Impl.Modes.X86.Ecb
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Camellia.X86.Dir

/-!
# Camellia on x86 (32-bit), bitsliced in XMM registers: sixteen blocks at a time

The modes' core (`core d`, `Impl/Modes/X86/Seq.lean`) of the baseline's
Camellia, in SSE2. A 64-bit half of each of sixteen blocks is held in eight
*planes* of 128 bits, in slots of the scratch buffer (16 bytes each, at
`sb`): bit `b` of 16-bit lane `i` of plane `j` is bit `j` of byte `i` of the
half, from the most significant, in block `b`. So the P-function is XORs of
a plane with its lanes shuffled (`pPlane`).

A round (`round`): the planes of one half XORed with the subkey's, those of
the lanes of `SBOX4` (3 and 6) rotated by one (`roundIn`); a circuit for
`SBOX1` on all the lanes (`sboxCode`); and for each plane the output's, of
the lanes of `SBOX2` and `SBOX3` the plane below or above, through the
P-function, XORed into the other half's (`roundOut`). The circuit has no
NOT: it is `SBOX1` of its input XORed with `0xc5`, XORed with `0x6e`. The
first is in the subkeys, the second in the output's selection (`sel`, whose
`pandn` complements the planes of `0x6e`'s bits).

A subkey (`prepare`) is a byte in each 16-bit lane, XORed with a constant
(byte 128 of the table) that the input's rotation turns into `0xc5`; plane
`j` of it is bit `j` of each lane copied through the lane (`kPlane`). FL,
FL⁻¹ and the whitening, whose input no S-box follows, take the constant off
again (`ldK`).

`crypt` calls the block function, an internal function, which the modes'
loops for groups of sixteen, eight, four and two blocks and for one
(`levels`) share: it costs the same for any number of them. Its constants
are in the static `table`, whose address `prepare` keeps in a slot.

Every address depends only on the loops' counts and the pointers.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86.Sse

open VG.X86
open VG.Impl.Modes.X86 (sb at_ argOp Core)

/-! ## The slots, and the table -/

/-- The slots of 16 bytes: the S-box's planes (0–7) and spills (8–25), the
table's address (`tblSlot`), the planes of the two halves (`d1`, `d2`), the
blocks (`bufS`) and the subkeys (`keyS`). -/
def tblSlot : Nat := 26
def d1 : Nat := 28
def d2 : Nat := 36
def bufS : Nat := 44
def keyS : Nat := 60

def tableName : String := "VG_CAMELLIA_SSE2"

/-- The masks of the transposes (bytes 0 to 63: the low byte of every 16-bit
lane, and every second bit, pair of bits and half byte), of the lanes whose
input an S-box rotates (64), of the lanes of `SBOX1` and `SBOX4`, `SBOX2`
and `SBOX3` (80, 96 and 112), the subkeys' constant (128), the key
schedule's constants `Sigma1 … Sigma6` as subkeys (144), and the low bit of
every lane (240). -/
def table : List (BitVec 64) := [
  0x00ff00ff00ff00ff, 0x00ff00ff00ff00ff,
  0x5555555555555555, 0x5555555555555555,
  0x3333333333333333, 0x3333333333333333,
  0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f,
  0xffff000000000000, 0x0000ffff00000000,
  0xffff00000000ffff, 0xffffffff00000000,
  0x00000000ffff0000, 0x000000000000ffff,
  0x0000ffff00000000, 0x00000000ffff0000,
  0x00e200c500c500c5, 0x00c500e200c500c5,
  0x009d00a3005b0065, 0x004e0072000900fe,
  0x00ba002d00bf0073, 0x00770091006f0089,
  0x00cd00f2002a0003, 0x007b0060008a002c,
  0x00470096003a0091, 0x00d9008d00160034,
  0x001800e2002000d5, 0x00d800cf00ad001b,
  0x0020004d00930075, 0x0038002300230076,
  0x0001000100010001, 0x0001000100010001]

/-- The table, and the subkeys. -/
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

/-! ## A round -/

/-- `SBOX1` of the planes in slots 0–7 XORed with `0xc5`, XORed with `0x6e`,
in the same slots. -/
def sboxCode : List Instr := [
  ldS .xmm7 1, ldS .xmm6 6, x .pxor .xmm6 .xmm7, ldS .xmm5 3, ldS .xmm4 6, x .pxor .xmm4 .xmm5, ldS .xmm3 5,
  x .pxor .xmm3 .xmm5, ldS .xmm5 5, x .pxor .xmm5 .xmm6, ldS .xmm2 7, x .pxor .xmm2 .xmm3, ldS .xmm1 7,
  x .pxor .xmm1 .xmm7, ldS .xmm0 0, stS 8 .xmm1, ldS .xmm1 7, x .pxor .xmm1 .xmm0, stS 9 .xmm5,
  x .movdqa .xmm5 .xmm2, x .pand .xmm5 .xmm1, stS 10 .xmm2, x .movdqa .xmm2 .xmm7, x .pxor .xmm2 .xmm1,
  x .pxor .xmm3 .xmm2, stS 11 .xmm5, ldS .xmm5 4, x .pxor .xmm5 .xmm7, ldS .xmm7 2, stS 12 .xmm3, ldS .xmm3 4,
  x .pxor .xmm3 .xmm7, x .pxor .xmm6 .xmm3, stS 13 .xmm1, x .movdqa .xmm1 .xmm6, x .pand .xmm1 .xmm5,
  stS 14 .xmm5, x .movdqa .xmm5 .xmm7, x .pxor .xmm5 .xmm2, x .pxor .xmm2 .xmm4, stS 15 .xmm6,
  x .movdqa .xmm6 .xmm7, x .pxor .xmm6 .xmm2, x .movdqa .xmm7 .xmm2, x .pand .xmm7 .xmm5, stS 16 .xmm5,
  ldS .xmm5 4, x .pxor .xmm5 .xmm2, stS 17 .xmm2, x .movdqa .xmm2 .xmm0, x .pand .xmm2 .xmm6, ldS .xmm0 5,
  x .pxor .xmm0 .xmm6, stS 18 .xmm6, ldS .xmm6 5, x .pxor .xmm6 .xmm3, stS 19 .xmm0, x .movdqa .xmm0 .xmm6,
  x .pand .xmm0 .xmm5, x .pxor .xmm1 .xmm0, stS 20 .xmm5, x .movdqa .xmm5 .xmm4, x .pxor .xmm5 .xmm3,
  stS 21 .xmm5, ldS .xmm5 13, x .pxor .xmm5 .xmm4, x .pxor .xmm3 .xmm5, stS 22 .xmm3, ldS .xmm3 9,
  x .pand .xmm3 .xmm5, x .pxor .xmm3 .xmm0, ldS .xmm0 8, x .pxor .xmm0 .xmm4, stS 23 .xmm5,
  x .movdqa .xmm5 .xmm0, x .pand .xmm5 .xmm4, x .pxor .xmm7 .xmm5, x .pxor .xmm2 .xmm5, x .pxor .xmm3 .xmm2,
  ldS .xmm5 12, x .pxor .xmm5 .xmm3, x .pxor .xmm1 .xmm7, ldS .xmm3 19, x .pxor .xmm3 .xmm1,
  x .movdqa .xmm1 .xmm3, x .pxor .xmm1 .xmm5, stS 19 .xmm4, ldS .xmm4 2, x .pxor .xmm4 .xmm0, stS 12 .xmm0,
  ldS .xmm0 17, x .pxor .xmm0 .xmm6, stS 24 .xmm6, ldS .xmm6 21, x .pand .xmm6 .xmm0, stS 25 .xmm0,
  ldS .xmm0 11, x .pxor .xmm0 .xmm6, x .pxor .xmm0 .xmm2, x .pxor .xmm0 .xmm4, ldS .xmm4 0, ldS .xmm2 15,
  x .pxor .xmm2 .xmm4, ldS .xmm4 22, x .pand .xmm4 .xmm2, x .pxor .xmm4 .xmm6, x .pxor .xmm4 .xmm7,
  ldS .xmm7 8, x .pxor .xmm7 .xmm4, x .movdqa .xmm4 .xmm7, x .pxor .xmm4 .xmm0, x .pand .xmm7 .xmm3,
  x .movdqa .xmm6 .xmm0, x .pxor .xmm6 .xmm7, x .pand .xmm6 .xmm1, x .pxor .xmm6 .xmm5, x .pxor .xmm7 .xmm5,
  x .pxor .xmm3 .xmm6, ldS .xmm1 13, x .pand .xmm1 .xmm6, stS 13 .xmm1, ldS .xmm1 10, x .pand .xmm1 .xmm6,
  stS 10 .xmm1, x .movdqa .xmm1 .xmm7, x .pxor .xmm1 .xmm6, x .pand .xmm5 .xmm1, x .pxor .xmm3 .xmm5,
  x .pxor .xmm5 .xmm7, ldS .xmm1 22, x .pand .xmm1 .xmm3, x .pand .xmm2 .xmm3, x .pand .xmm7 .xmm4,
  x .pxor .xmm7 .xmm0, x .pand .xmm5 .xmm7, x .pxor .xmm4 .xmm5, ldS .xmm5 14, x .pand .xmm5 .xmm4,
  ldS .xmm0 15, x .pand .xmm0 .xmm4, stS 15 .xmm0, ldS .xmm0 9, x .pand .xmm0 .xmm7, stS 9 .xmm0, ldS .xmm0 23,
  x .pand .xmm0 .xmm7, stS 23 .xmm2, x .movdqa .xmm2 .xmm7, x .pxor .xmm2 .xmm4, stS 14 .xmm4, ldS .xmm4 24,
  x .pand .xmm4 .xmm2, stS 24 .xmm4, ldS .xmm4 20, x .pand .xmm4 .xmm2, x .pxor .xmm0 .xmm4,
  x .pxor .xmm4 .xmm5, x .pxor .xmm4 .xmm1, x .pxor .xmm7 .xmm6, ldS .xmm5 12, x .pand .xmm5 .xmm7,
  ldS .xmm2 19, x .pand .xmm2 .xmm7, x .pxor .xmm6 .xmm3, stS 19 .xmm4, ldS .xmm4 14, x .pxor .xmm4 .xmm3,
  x .pxor .xmm7 .xmm4, ldS .xmm3 18, x .pand .xmm3 .xmm4, stS 18 .xmm5, ldS .xmm5 0, x .pand .xmm5 .xmm4,
  ldS .xmm4 16, x .pand .xmm4 .xmm7, x .pxor .xmm1 .xmm4, ldS .xmm4 17, x .pand .xmm4 .xmm7,
  x .pxor .xmm2 .xmm1, x .pxor .xmm1 .xmm0, x .pxor .xmm3 .xmm1, x .pxor .xmm0 .xmm2, ldS .xmm1 13,
  x .pxor .xmm1 .xmm0, ldS .xmm0 25, x .pand .xmm0 .xmm6, ldS .xmm7 21, x .pand .xmm7 .xmm6,
  x .pxor .xmm2 .xmm7, x .pxor .xmm5 .xmm7, x .pxor .xmm7 .xmm3, ldS .xmm6 18, x .pxor .xmm6 .xmm0,
  ldS .xmm0 10, x .pxor .xmm0 .xmm6, stS 10 .xmm7, ldS .xmm7 23, x .pxor .xmm7 .xmm6, x .pxor .xmm3 .xmm0,
  x .pxor .xmm3 .xmm5, x .pxor .xmm0 .xmm1, x .pxor .xmm7 .xmm4, ldS .xmm6 15, x .pxor .xmm6 .xmm4,
  x .pxor .xmm7 .xmm1, ldS .xmm4 9, x .pxor .xmm4 .xmm6, x .pxor .xmm0 .xmm4, x .pxor .xmm5 .xmm4,
  ldS .xmm4 19, x .pxor .xmm4 .xmm5, ldS .xmm5 24, x .pxor .xmm5 .xmm2, x .pxor .xmm6 .xmm5, ldS .xmm5 18,
  x .pxor .xmm5 .xmm6, stS 0 .xmm3, stS 1 .xmm2, stS 2 .xmm5, stS 4 .xmm0, stS 5 .xmm4, stS 6 .xmm1,
  stS 7 .xmm7, ldS .xmm0 10, stS 3 .xmm0]

/-- Plane `j` of the subkey in `k`, to `t`. -/
def kPlane (t k : XReg) (j : Nat) : List Instr := [mv t k, sh .pslld t (15 - j), sh .psraw t 15]

/-- Plane `k` (from slot `src + k`) XORed with the subkey's, its lanes of
`SBOX4` the plane's before (in `prev`), to slot `k`. -/
def inStep (src k : Nat) (a prev : XReg) : List Instr :=
  [ldS a (src + k)] ++ kPlane .xmm2 .xmm6 k ++
    [x .pxor a .xmm2, x .pxor prev a, x .pand prev .xmm7, x .pxor prev a, stS k prev]

/-- The S-box's input of a round, with the subkey at byte `ko` from `kr`. -/
def roundIn (src ko : Nat) : List Instr :=
  [tb .xmm7 64, ld .xmm6 kr ko, ldS .xmm1 (src + 7)] ++ kPlane .xmm2 .xmm6 7 ++ [x .pxor .xmm1 .xmm2, mv .xmm5 .xmm1] ++
  (List.range 7).flatMap (fun k => if k % 2 = 0 then inStep src k .xmm0 .xmm1 else inStep src k .xmm1 .xmm0) ++
  [x .pxor .xmm0 .xmm5, x .pand .xmm0 .xmm7, x .pxor .xmm0 .xmm5, stS 7 .xmm0]

/-- Bit `k` of the S-box's output constant. -/
def wBit (k : Nat) : Bool := (0x6e >>> k) % 2 = 1

/-- The lanes `m` of the S-box's output plane `k`. -/
def sel (d m : XReg) (k : Nat) : List Instr := [ldS d k, x (if wBit k then .pandn else .pand) d m]

/-- The P-function of the plane in `xmm0`, to `xmm2`. -/
def pPlane : List Instr :=
  [.xop (.pshufd .xmm1 .xmm0 0xEE), .xop (.pshufd .xmm2 .xmm0 0x44), x .pxor .xmm2 .xmm1, .xop (.pshufd .xmm3 .xmm1 0xB1),
   x .pxor .xmm2 .xmm3, x .pxor .xmm1 .xmm2, .xop (.pshuflw .xmm3 .xmm2 0x39), x .pxor .xmm1 .xmm3,
   .xop (.pshufd .xmm3 .xmm1 0xB1), x .pxor .xmm2 .xmm3, x .punpcklqdq .xmm2 .xmm1]

/-- Plane `k` of the round's output, into that of the other half. -/
def outStep (dst k : Nat) : List Instr :=
  sel .xmm0 .xmm5 k ++ sel .xmm1 .xmm6 ((k + 7) % 8) ++ [x .pxor .xmm0 .xmm1] ++ sel .xmm1 .xmm7 ((k + 1) % 8) ++
  [x .pxor .xmm0 .xmm1] ++ pPlane ++ [ldS .xmm3 (dst + k), x .pxor .xmm2 .xmm3, stS (dst + k) .xmm2]

def roundOut (dst : Nat) : List Instr :=
  [tb .xmm5 80, tb .xmm6 96, tb .xmm7 112] ++ (List.range 8).flatMap (outStep dst)

/-- A round of the half at `src`, into the one at `dst`. -/
def round (ko src dst : Nat) : List Instr := roundIn src ko ++ sboxCode ++ roundOut dst

/-! ## FL, FL⁻¹ and the whitening -/

/-- The subkey at byte `ko` from `kr`, to `xmm6`. -/
def ldK (ko : Nat) : List Instr := [ld .xmm6 kr ko, tb .xmm5 128, x .pxor .xmm6 .xmm5]

/-- Plane `j` of `x2 ^= (x1 & k1) <<< 1`. -/
def flRot (d j : Nat) : List Instr :=
  let i := (j + 7) % 8
  [ldS .xmm0 (d + i)] ++ kPlane .xmm1 .xmm6 i ++ [x .pand .xmm0 .xmm1] ++
  (if j = 0 then [.xop (.pshuflw .xmm0 .xmm0 0x39)] else []) ++
  [sh .pslldq .xmm0 8, ldS .xmm2 (d + j), x .pxor .xmm2 .xmm0, stS (d + j) .xmm2]

/-- Plane `j` of `x1 ^= x2 | k2`. -/
def flOr (d j : Nat) : List Instr :=
  [ldS .xmm0 (d + j)] ++ kPlane .xmm1 .xmm6 j ++ [x .por .xmm1 .xmm0, sh .psrldq .xmm1 8, ldS .xmm2 (d + j),
    x .pxor .xmm2 .xmm1, stS (d + j) .xmm2]

def fl (ko d : Nat) : List Instr := ldK ko ++ (List.range 8).flatMap (flRot d) ++ (List.range 8).flatMap (flOr d)
def flinv (ko d : Nat) : List Instr := ldK ko ++ (List.range 8).flatMap (flOr d) ++ (List.range 8).flatMap (flRot d)

/-- The planes at `d` XORed with the subkey's. -/
def whiten (ko d : Nat) : List Instr :=
  ldK ko ++ (List.range 8).flatMap fun j =>
    [ldS .xmm0 (d + j)] ++ kPlane .xmm1 .xmm6 j ++ [x .pxor .xmm0 .xmm1, stS (d + j) .xmm0]

/-! ## The transposes -/

/-- The bits of slot `p` that the mask in `xmm7` shifted left by `n` has,
swapped with those of slot `q` that the mask has. -/
def swap (n p q : Nat) : List Instr :=
  [ldS .xmm0 p, ldS .xmm1 q, mv .xmm2 .xmm0, sh .psrlq .xmm2 n, x .pxor .xmm2 .xmm1, x .pand .xmm2 .xmm7, x .pxor .xmm1 .xmm2,
   sh .psllq .xmm2 n, x .pxor .xmm0 .xmm2, stS p .xmm0, stS q .xmm1]

/-- The 8 × 8 bit matrices of the slots from `d` on, transposed. -/
def ortho (d : Nat) : List Instr :=
  [tb .xmm7 16] ++ [0, 2, 4, 6].flatMap (fun i => swap 1 (d + i) (d + i + 1)) ++
  [tb .xmm7 32] ++ [0, 1, 4, 5].flatMap (fun i => swap 2 (d + i) (d + i + 2)) ++
  [tb .xmm7 48] ++ [0, 1, 2, 3].flatMap (fun i => swap 4 (d + i) (d + i + 4))

/-- The halves of blocks `r` and `r + 8`, a byte of each in each 16-bit lane. -/
def inPair (r : Nat) : List Instr :=
  [ldS .xmm0 (bufS + r), ldS .xmm1 (bufS + 8 + r),
   mv .xmm2 .xmm0, x .pand .xmm2 .xmm7, mv .xmm3 .xmm1, x .pand .xmm3 .xmm7, sh .pslld .xmm3 8, x .pxor .xmm2 .xmm3,
   sh .psrld .xmm0 8, x .pand .xmm0 .xmm7, mv .xmm4 .xmm7, x .pandn .xmm4 .xmm1, x .pxor .xmm0 .xmm4,
   mv .xmm3 .xmm2, x .punpcklwd .xmm2 .xmm0, x .punpckhwd .xmm3 .xmm0, stS (d1 + r) .xmm2, stS (d2 + r) .xmm3]

/-- The blocks of the buffer to the planes of their halves. -/
def blocksIn : List Instr := [tb .xmm7 0] ++ (List.range 8).flatMap inPair ++ ortho d1 ++ ortho d2

/-- Blocks `r` and `r + 8` from their halves, the second first. -/
def outPair (r : Nat) : List Instr :=
  [ldS .xmm0 (d2 + r), ldS .xmm1 (d1 + r),
   .xop (.pshuflw .xmm0 .xmm0 0xD8), .xop (.pshufhw .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm0 .xmm0 0xD8),
   .xop (.pshuflw .xmm1 .xmm1 0xD8), .xop (.pshufhw .xmm1 .xmm1 0xD8), .xop (.pshufd .xmm1 .xmm1 0xD8),
   mv .xmm2 .xmm0, x .punpcklqdq .xmm0 .xmm1, x .punpckhqdq .xmm2 .xmm1,
   mv .xmm3 .xmm0, x .pand .xmm3 .xmm7, mv .xmm4 .xmm2, x .pand .xmm4 .xmm7, sh .pslld .xmm4 8, x .pxor .xmm3 .xmm4,
   sh .psrld .xmm0 8, x .pand .xmm0 .xmm7, mv .xmm4 .xmm7, x .pandn .xmm4 .xmm2, x .pxor .xmm0 .xmm4,
   stS (bufS + r) .xmm3, stS (bufS + 8 + r) .xmm0]

/-- The planes of the halves back to the blocks of the buffer, the halves swapped. -/
def blocksOut : List Instr := ortho d1 ++ ortho d2 ++ [tb .xmm7 0] ++ (List.range 8).flatMap outPair

/-! ## The block function -/

def cryptHead : List Instr := blocksIn ++ whiten 0 d1 ++ whiten 16 d2

/-- A pair of rounds, on by its two subkeys, and the count of the pairs. -/
def pairB : List Instr := round 32 d1 d2 ++ round 48 d2 d1 ++ [.alu .add kr (.imm 32), .alu .sub .edx (.imm 1)]

/-- A group of six rounds, and the count of the groups. -/
def group : Prog isa :=
  .seq (.block [.mov .edx (.imm 3)]) (.seq (.loop (.block pairB) .ne) (.block [.alu .sub .ecx (.imm 1)]))

/-- FL and FL⁻¹ between groups, and the flags of the count. -/
def layer : List Instr := fl 32 d1 ++ flinv 48 d2 ++ [.alu .add kr (.imm 32), .alu .test .ecx (.reg .ecx)]

def cryptTail : List Instr := whiten 32 d2 ++ whiten 48 d1 ++ blocksOut

/-- The block function on the sixteen blocks of the buffer, with the groups
of rounds in `ecx`, the table in `tbr` and the subkeys in `kr`. -/
def cryptFn : Prog isa :=
  .seq (.block cryptHead) (.seq
    (.loop (.seq group (.ite .e (.block []) (.block layer))) .ne) (.block cryptTail))

/-- The table, the groups of rounds (from the number of rounds, `argOp 1`)
and the subkeys. -/
def cryptSetup : List Instr :=
  [.mov tbr (.mem (at_ sb (16 * tblSlot))), .mov .ecx (.mem (argOp 1)), .shift .shr .ecx 3, .alu .add .ecx (.imm 1),
   .mov kr (.reg sb), .alu .add kr (.imm 960)]

/-- The core's code: a call of the block function. -/
def crypt : Prog isa := .seq (.block cryptSetup) (.call "vg_camellia_crypt16_sse2" cryptFn)

/-! ## The subkeys -/

/-- The subkey at `[eax]` to the next place. -/
def prepOne : List Instr :=
  [.movqLoad .xmm0 (at_ .eax 0), mv .xmm1 .xmm0, x .pand .xmm0 .xmm7, sh .psrld .xmm1 8, x .pand .xmm1 .xmm7,
   x .punpcklwd .xmm0 .xmm1, x .pxor .xmm0 .xmm6, stx kr 0 .xmm0, .alu .add kr (.imm 16)]

/-- The schedule's next subkey. -/
def addE : Instr := .alu .add .eax (.imm 8)
/-- The schedule's subkey before. -/
def subE : Instr := .alu .sub .eax (.imm 8)

/-- The table's address (in `eax`) to its slot, the schedule and the number
of rounds from the stack arguments, and the constants; whether the rounds
are 18. -/
def prepHead : List Instr :=
  [.store (at_ sb (16 * tblSlot)) .eax, .mov tbr (.reg .eax), .mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)),
   .mov kr (.reg sb), .alu .add kr (.imm 960), tb .xmm7 0, tb .xmm6 128, .alu .cmp .ecx (.imm 18)]

/-- The schedule's subkeys in order. -/
def prepEnc : Prog isa :=
  .seq (.ite .e (.block [.mov .ecx (.imm 26)]) (.block [.mov .ecx (.imm 34)]))
    (.loop (.block (prepOne ++ [addE, .alu .sub .ecx (.imm 1)])) .ne)

/-- The schedule's subkeys in decryption's order (`decPerm`): the last two,
the rest but the first two from the last back, then the first two. -/
def prepDec : Prog isa :=
  .seq (.ite .e (.block [.mov .ecx (.imm 22), .alu .add .eax (.imm 192)])
      (.block [.mov .ecx (.imm 30), .alu .add .eax (.imm 256)]))
    (.seq (.block (prepOne ++ [addE] ++ prepOne ++ [.alu .sub .eax (.imm 16)]))
      (.seq (.loop (.block (prepOne ++ [subE, .alu .sub .ecx (.imm 1)])) .ne)
        (.block ([subE] ++ prepOne ++ [addE] ++ prepOne))))

/-- The subkeys of the schedule (`argOp 0`), in the order of the direction,
and the table's address, in their slots. -/
def prepare (d : Dir) : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.seq (.block prepHead) (match d with | .encrypt => prepEnc | .decrypt => prepDec))

/-! ## The core, and the modes -/

/-- The core's slots, in doublewords. -/
def slots : Nat := 376

/-- Camellia's core of sixteen blocks for the direction `d`. -/
def core (d : Dir) : Core where
  prepare := prepare d
  crypt := crypt
  slots := slots
  total := slots + 10
  buf := 176
  G := 16
  bw := 4
  stack := 4
  ka := 2

/-- The sizes of the groups of blocks the modes whose blocks are independent
take, in turn, before single blocks. -/
def levels : List Nat := [16, 8, 4, 2]

/-- `vg_camellia_ecb_encrypt` or `vg_camellia_ecb_decrypt`, with its scratch
buffer as the fifth argument. -/
def ecb (d : Dir) : Prog isa := (core d).ecbLevels levels

/-- `vg_camellia_cbc_encrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcEncryptChained : Prog isa := (core .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_camellia_cbc_decrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcDecryptChained : Prog isa :=
  (core .decrypt).seqLevels (Modes.Mode.cbcDecWide 4) levels (Modes.Mode.cbcDecChained 4)

/-- `vg_camellia_ctr`, with its scratch buffer as the sixth argument. -/
def ctr : Prog isa := (core .encrypt).seqLevels Modes.Mode.ctrWide levels Modes.Mode.ctrEarly

/-- `vg_camellia_ofb`, with its scratch buffer as the sixth argument. -/
def ofb : Prog isa := (core .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_camellia_cfb128_encrypt`, with its scratch buffer as the sixth argument. -/
def cfbEncrypt : Prog isa := (core .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_camellia_cfb128_decrypt`, with its scratch buffer as the sixth argument. -/
def cfbDecrypt : Prog isa :=
  (core .encrypt).seqLevels (Modes.Mode.cfbDecWide 4) levels (Modes.Mode.cfbDecEarly 4)

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (core .encrypt).seqFinal (Modes.Mode.cfbEnc 4)

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (core .encrypt).seqFinal (Modes.Mode.cfbDec 4)

/-- `vg_camellia_ofb_final`. -/
def ofbFinal : Prog isa := (core .encrypt).seqFinal (Modes.Mode.ofb 4)

end VG.Impl.Camellia.X86.Sse
