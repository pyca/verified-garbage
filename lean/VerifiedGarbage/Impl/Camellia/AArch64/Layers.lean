import VerifiedGarbage.Impl.Camellia.AArch64.Sbox
import VerifiedGarbage.Impl.Aes.AArch64.Linear

/-!
# The layers of bitsliced Camellia on AArch64

As on x86-64 (`Impl/Camellia/X86_64/Layers.lean`, which describes the
representation): eight blocks at a time, each 64-bit half as eight planes
in `q 0 … q 7` (plane `j` holds bit `j` of the half's eight bytes in each
of the eight blocks), the S-boxes as the circuit `Circuit.sbox`, the
P-function and the rotations of FL and FLINV as masked rotations of whole
planes. AArch64 has no memory operands for logic instructions, so each
operand in memory (a subkey's plane, a mask, the other half) is loaded into
a temporary first; the masks of a layer are loaded once for the layer.

The scratch buffer at `x5` holds, in 8-byte slots: the S-box's spills
(0–47); the masks of the layers (48–52); the planes of `D1` (64–71) and
`D2` (72–79): the rounds' working space, below slot 96; then the bitsliced
subkeys, eight planes each, in the order the rounds use them (from slot
96); the callee-saved registers `x19`–`x28` (368–377); and the tail buffer
(378–393, eight blocks), through which every group is copied. The key
schedule (`ExpandKey.lean`) uses the same layout, with its 128-bit values in
the tail buffer.
-/

namespace VG.Impl.Camellia.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

/-! ## Slots -/

def evenSlot : Nat := 48
def oddSlot : Nat := 49
/-- The bytes of `SBOX4` (positions `t4`, `t7`). -/
def m4Slot : Nat := 50
/-- The bytes of `SBOX2` (positions `t2`, `t5`). -/
def m2Slot : Nat := 51
/-- The bytes of `SBOX3` (positions `t3`, `t6`). -/
def m3Slot : Nat := 52
def d1Slot : Nat := 64
def d2Slot : Nat := 72
def keySlot : Nat := 96
/-- After the table of 34 subkeys. -/
def endSlot : Nat := keySlot + 8 * 34
def savedSlot : Nat := endSlot
def tailSlot : Nat := savedSlot + 10

/-- The number of slots: the tail buffer is the last 16. -/
def slots : Nat := tailSlot + 16

def layerMasks : List (Nat × BitVec 64) :=
  [(evenSlot, 0x00FF00FF00FF00FF), (oddSlot, 0xFF00FF00FF00FF00),
   (m4Slot, 0x00FFFF0000000000), (m2Slot, 0x0000000000FFFF00), (m3Slot, 0x000000FFFF000000)]

/-- The masks to their slots, through `t0`. -/
def setSlots (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => imm t0 v ++ [stS k t0]

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.x19, savedSlot), (.x20, savedSlot + 1), (.x21, savedSlot + 2), (.x22, savedSlot + 3),
   (.x23, savedSlot + 4), (.x24, savedSlot + 5), (.x25, savedSlot + 6), (.x26, savedSlot + 7),
   (.x27, savedSlot + 8), (.x28, savedSlot + 9)]

def saveRegs : List Instr := savedRegs.map fun (r, k) => stS k r
def restoreRegs : List Instr := savedRegs.map fun (r, k) => ldS r k

/-! ## Between words and planes -/

/-- The masks of the transposes, in `m 1`, `m 2` and `m 4`–`m 6`. -/
def bsMasks : List (Nat × BitVec 64) :=
  [(1, 0x00000000FFFF0000), (2, 0x0000FF000000FF00),
   (4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]

/-- From eight little-endian words of a half (block `b`'s in `q b`) to its
planes (plane `j` in `q j`). Uses the mask registers and `t0`. -/
def toBs : List Instr := setMasks bsMasks ++ zip1 ++ zip2 ++ ortho

/-- From the planes back to the eight words. -/
def fromBs : List Instr := setMasks bsMasks ++ ortho ++ zip2 ++ zip1

/-! ## A round -/

/-- Load the mask in slot `k` into `r`. -/
def ldMask (r : Reg) (k : Nat) : Instr := ldS r k

/-- XOR the subkey's planes, words `off … off + 7` at `kp`, into the state. -/
def keyXor (off : Nat) : List Instr :=
  (List.range 8).flatMap fun j => [.ldr .x t0 kp (8 * (off + j)), eorR (q j) (q j) t0]

/-- In the bytes of the mask in slot `m`, plane `j` takes plane `j - 1`
(cyclically): the bytes are rotated left by one bit. -/
def rotUp (mk : Nat) : List Instr :=
  [ldMask t2 mk, movR t1 (q 7)] ++
  ((List.range 7).reverse.flatMap fun i =>
    [eorR t0 (q (i + 1)) (q i), andR t0 t0 t2, eorR (q (i + 1)) (q (i + 1)) t0]) ++
  [eorR t0 (q 0) t1, andR t0 t0 t2, eorR (q 0) (q 0) t0]

/-- In the bytes of the mask in slot `m`, plane `j` takes plane `j + 1`
(cyclically): the bytes are rotated right by one bit. -/
def rotDown (mk : Nat) : List Instr :=
  [ldMask t2 mk, movR t1 (q 0)] ++
  ((List.range 7).flatMap fun i =>
    [eorR t0 (q i) (q (i + 1)), andR t0 t0 t2, eorR (q i) (q i) t0]) ++
  [eorR t0 (q 7) t1, andR t0 t0 t2, eorR (q 7) (q 7) t0]

/-- `SBOX4[x] = SBOX1[x <<< 1]`: rotate its input bytes. -/
def inSel : List Instr := rotUp m4Slot

/-- `SBOX2[x] = SBOX1[x] <<< 1` and `SBOX3[x] = SBOX1[x] <<< 7`: rotate
their output bytes. -/
def outSel : List Instr := rotUp m2Slot ++ rotDown m3Slot

/-- One step of the P-function on plane `w`: `w ^= (w ⋙ s) & mk`. -/
def pStep (w : Reg) (s : Nat) (mk : Reg) : List Instr := [rorI t0 w s, andR t0 t0 mk, eorR w w t0]

/-- The P-function on each plane, with the even bytes' mask in `t2` and the
odd bytes' in `u7`. -/
def pLayer : List Instr :=
  [ldMask t2 evenSlot, ldMask u7 oddSlot] ++
  (List.range 8).flatMap fun j =>
    pStep (q j) 8 t2 ++ pStep (q j) 40 t2 ++ pStep (q j) 56 u7 ++ pStep (q j) 8 u7 ++
      pStep (q j) 40 t2

/-- XOR the F-function's output into the other half, at slots `d … d + 7`,
and store it there; the state is left holding it. -/
def feistel (d : Nat) : List Instr :=
  (List.range 8).flatMap fun j => [ldS t0 (d + j), eorR (q j) (q j) t0, stS (d + j) (q j)]

/-- A round: the half in the state through the F-function with the subkey
at word `off` of `kp`, XORed into the other half at slot `d`. -/
def round (off d : Nat) : List Instr :=
  keyXor off ++ inSel ++ sboxCode ++ outSel ++ pLayer ++ feistel d

/-! ## FL and FLINV -/

/-- One plane of `flRot`: `q j ^= ((x & k) ⋙ s) & odd`, `x` in `src`,
`k` word `kw` at `kp`, the odd bytes' mask in `t2`. -/
def flRotStep (j : Nat) (src : Reg) (kw s : Nat) : List Instr :=
  [.ldr .x u7 kp (8 * kw), andR t0 src u7, rorI t0 t0 s, andR t0 t0 t2, eorR (q j) (q j) t0]

/-- Planes `n` down to 1 of `flRot`, each from plane `j - 1` below it. -/
def flRotDesc (off : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => flRotStep (n + 1) (q n) (off + n) 56 ++ flRotDesc off n

/-- `x2 ^= (x1 & k1) <<< 1`, with the subkey's planes at word `off` of
`kp`, as on x86-64. -/
def flRot (off : Nat) : List Instr :=
  [ldMask t2 oddSlot, movR t1 (q 7)] ++ flRotDesc off 7 ++ flRotStep 0 t1 (off + 7) 8

/-- One plane of `flOr`: `q j ^= ((q j | k) ⋙ 8) & even`, `k` word `kw` at
`kp`, the even bytes' mask in `t2`. -/
def flOrStep (j kw : Nat) : List Instr :=
  [.ldr .x u7 kp (8 * kw), orrR t0 (q j) u7, rorI t0 t0 8, andR t0 t0 t2, eorR (q j) (q j) t0]

/-- Planes `n - 1` down to 0 of `flOr`. -/
def flOrDesc (off : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => flOrStep n (off + n) ++ flOrDesc off n

/-- `x1 ^= x2 | k2`, with the subkey's planes at word `off` of `kp`. -/
def flOr (off : Nat) : List Instr := ldMask t2 evenSlot :: flOrDesc off 8

/-- FL on the state. -/
def flCode (off : Nat) : List Instr := flRot off ++ flOr off

/-- FLINV on the state. -/
def flinvCode (off : Nat) : List Instr := flOr off ++ flRot off

/-- Load the planes at slots `d … d + 7` into the state. -/
def loadHalf (d : Nat) : List Instr := (List.range 8).map fun j => ldS (q j) (d + j)

/-- Store the state to slots `d … d + 7`. -/
def storeHalf (d : Nat) : List Instr := (List.range 8).map fun j => stS (d + j) (q j)

/-- FLINV on `D2` with the subkey at word 8 of `kp`, then FL on `D1` with the
one at word 0, and on to the next entries; the state is left holding `D1`. -/
def flLayer : List Instr :=
  loadHalf d2Slot ++ flinvCode 8 ++ storeHalf d2Slot ++
  loadHalf d1Slot ++ flCode 0 ++ storeHalf d1Slot ++ ([.addImm .x kp kp 128] : List Instr)

end VG.Impl.Camellia.AArch64
