import VerifiedGarbage.Impl.Camellia.X86_64.Sbox
import VerifiedGarbage.Impl.Aes.X86_64.Linear

/-!
# The layers of bitsliced Camellia on x86-64

Eight blocks at a time. A 64-bit half of the blocks (`D1` or `D2`, RFC 3713
§2.3) is eight 64-bit words, *planes*: plane `j` holds bit `j` of the 64
bytes, byte `c` of the half of block `b` at bit position `8c + b`. Within a
plane the bytes are interleaved: byte `c` holds the half's byte `pos c`
(`t1 … t8` numbered from 0), `0 4 1 5 2 6 3 7`, the left 32 bits in the
even bytes and the right 32 in the odd ones. AES's `zip1` and `zip2` put a
little-endian word of the half's bytes in that order, and its `ortho`
transposes eight such words (one per block) into the planes.

So the P-function (§2.4.1), which mixes the bytes, is five steps of a
plane XORed with a rotation of itself masked to its even or odd bytes, and
the 32-bit rotations of FL and FLINV (§2.4.2) are rotations of whole planes
by 8 bits. `SBOX2`, `SBOX3` and `SBOX4` are `SBOX1` with a rotation of the
output or input byte, that is a renaming of planes in the bytes that use
them, which a masked exchange of neighbouring planes makes.

The scratch buffer at `r9` holds, in 8-byte slots: all ones (slot 0, for the
S-box), the S-box's spills (1–47, also the masks of the transposes), the
masks of the layers (48–52), the planes of `D1` (64–71) and `D2` (72–79):
the rounds' working space, below slot 96; then the bitsliced subkeys, eight
planes each, in the order the rounds use them (from slot 96), the address
of the postwhitening's entry (368), the data pointer while the last blocks
are processed in the tail buffer (369), the callee-saved registers
(370–375), and the tail buffer (376–391, eight blocks).
-/

namespace VG.Impl.Camellia.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

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
def dataSlot : Nat := endSlot + 1
def countSlot : Nat := endSlot + 2
def savedSlot : Nat := endSlot + 3
def tailSlot : Nat := endSlot + 9

/-- The number of slots: the tail buffer is the last 16. -/
def slots : Nat := tailSlot + 16

def layerMasks : List (Nat × BitVec 64) :=
  [(evenSlot, 0x00FF00FF00FF00FF), (oddSlot, 0xFF00FF00FF00FF00),
   (m4Slot, 0x00FFFF0000000000), (m2Slot, 0x0000000000FFFF00), (m3Slot, 0x000000FFFF000000)]

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.rbx, savedSlot), (.rbp, savedSlot + 1), (.r12, savedSlot + 2), (.r13, savedSlot + 3),
   (.r14, savedSlot + 4), (.r15, savedSlot + 5)]

def saveRegs : List Instr := savedRegs.map fun (r, k) => st k r
def restoreRegs : List Instr := savedRegs.map fun (r, k) => movS r k

/-! ## Between words and planes -/

/-- The masks of the transposes, in slots 1, 2 and 4–6. -/
def bsMasks : List (Nat × BitVec 64) :=
  [(1, 0x00000000FFFF0000), (2, 0x0000FF000000FF00),
   (4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]

/-- From eight little-endian words of a half (block `b`'s in `q b`) to its
planes (plane `j` in `q j`). Uses only the temporary `t0`. -/
def toBs : List Instr := setMasks bsMasks ++ zip1 ++ zip2 ++ ortho

/-- From the planes back to the eight words. -/
def fromBs : List Instr := setMasks bsMasks ++ ortho ++ zip2 ++ zip1

/-! ## A round -/

/-- The register of the round key's entry. -/
def kp : Reg := .rsi

/-- The memory operand of word `k` of the entry at `kp`. -/
def keyAt (k : Nat) : MemOp := slotAt kp k

/-- XOR the subkey's planes, words `off … off + 7` at `kp`, into the state. -/
def keyXor (off : Nat) : List Instr :=
  (List.range 8).map fun j => .alu .xor (q j) (.mem (keyAt (off + j)))

/-- In the bytes of the mask in slot `m`, plane `j` takes plane `j - 1`
(cyclically): the bytes are rotated left by one bit. -/
def rotUp (m : Nat) : List Instr :=
  [movR t1 (q 7)] ++
  ((List.range 7).reverse.flatMap fun i =>
    [movR t0 (q (i + 1)), xorR t0 (q i), andS t0 m, xorR (q (i + 1)) t0]) ++
  [movR t0 (q 0), xorR t0 t1, andS t0 m, xorR (q 0) t0]

/-- In the bytes of the mask in slot `m`, plane `j` takes plane `j + 1`
(cyclically): the bytes are rotated right by one bit. -/
def rotDown (m : Nat) : List Instr :=
  [movR t1 (q 0)] ++
  ((List.range 7).flatMap fun i =>
    [movR t0 (q i), xorR t0 (q (i + 1)), andS t0 m, xorR (q i) t0]) ++
  [movR t0 (q 7), xorR t0 t1, andS t0 m, xorR (q 7) t0]

/-- `SBOX4[x] = SBOX1[x <<< 1]`: rotate its input bytes. -/
def inSel : List Instr := rotUp m4Slot

/-- `SBOX2[x] = SBOX1[x] <<< 1` and `SBOX3[x] = SBOX1[x] <<< 7`: rotate
their output bytes. -/
def outSel : List Instr := rotUp m2Slot ++ rotDown m3Slot

/-- One step of the P-function on plane `w`: `w ^= (w ⋙ s) & mask`. -/
def pStep (w : Reg) (s m : Nat) : List Instr := [movR t0 w, rorI t0 s, andS t0 m, xorR w t0]

/-- The P-function on each plane. -/
def pLayer : List Instr :=
  (List.range 8).flatMap fun j =>
    pStep (q j) 8 evenSlot ++ pStep (q j) 40 evenSlot ++ pStep (q j) 56 oddSlot ++
      pStep (q j) 8 oddSlot ++ pStep (q j) 40 evenSlot

/-- XOR the F-function's output into the other half, at slots `d … d + 7`,
and store it there; the state is left holding it. -/
def feistel (d : Nat) : List Instr :=
  (List.range 8).flatMap fun j => [xorS (q j) (d + j), st (d + j) (q j)]

/-- A round: the half in the state through the F-function with the subkey
at word `off` of `kp`, XORed into the other half at slot `d`. -/
def round (off d : Nat) : List Instr :=
  keyXor off ++ inSel ++ sboxCode ++ outSel ++ pLayer ++ feistel d

/-! ## FL and FLINV -/

def orK (d : Reg) (k : Nat) : Instr := .alu .or d (.mem (keyAt k))
def andK (d : Reg) (k : Nat) : Instr := .alu .and d (.mem (keyAt k))

/-- One plane of `flRot`: `q j ^= ((x & k) ⋙ s) & odd`, `x` in `src`,
`k` word `kw` at `kp`. -/
def flRotStep (j : Nat) (src : Reg) (kw s : Nat) : List Instr :=
  [movR t0 src, andK t0 kw, rorI t0 s, andS t0 oddSlot, xorR (q j) t0]

/-- Planes `n` down to 1 of `flRot`, each from plane `j - 1` below it. -/
def flRotDesc (off : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => flRotStep (n + 1) (q n) (off + n) 56 ++ flRotDesc off n

/-- `x2 ^= (x1 & k1) <<< 1`, with the subkey's planes at word `off` of
`kp`: plane `j` of the right half (odd bytes) takes plane `j - 1` of the
left (even bytes) one byte up, and plane 0 takes plane 7 one byte down,
which rotates the left half's bytes by one. Plane 7 is saved first, and the
planes are updated from 7 down, so that each step reads planes as they were. -/
def flRot (off : Nat) : List Instr :=
  [movR t1 (q 7)] ++ flRotDesc off 7 ++ flRotStep 0 t1 (off + 7) 8

/-- One plane of `flOr`: `q j ^= ((q j | k) ⋙ 8) & even`, `k` word `kw` at `kp`. -/
def flOrStep (j kw : Nat) : List Instr :=
  [movR t0 (q j), orK t0 kw, rorI t0 8, andS t0 evenSlot, xorR (q j) t0]

/-- Planes `n - 1` down to 0 of `flOr`. -/
def flOrDesc (off : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => flOrStep n (off + n) ++ flOrDesc off n

/-- `x1 ^= x2 | k2`, with the subkey's planes at word `off` of `kp`. -/
def flOr (off : Nat) : List Instr := flOrDesc off 8

/-- FL on the state. -/
def flCode (off : Nat) : List Instr := flRot off ++ flOr off

/-- FLINV on the state. -/
def flinvCode (off : Nat) : List Instr := flOr off ++ flRot off

/-- Load the planes at slots `d … d + 7` into the state. -/
def loadHalf (d : Nat) : List Instr := (List.range 8).map fun j => movS (q j) (d + j)

/-- Store the state to slots `d … d + 7`. -/
def storeHalf (d : Nat) : List Instr := (List.range 8).map fun j => st (d + j) (q j)

/-- FLINV on `D2` with the subkey at word 8 of `kp`, then FL on `D1` with the
one at word 0, and on to the next entries; the state is left holding `D1`. -/
def flLayer : List Instr :=
  loadHalf d2Slot ++ flinvCode 8 ++ storeHalf d2Slot ++
  loadHalf d1Slot ++ flCode 0 ++ storeHalf d1Slot ++ [.alu .add kp (.imm 128)]

end VG.Impl.Camellia.X86_64
