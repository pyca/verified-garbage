module

public import VerifiedGarbage.Impl.Camellia.Arm.Sbox
public import VerifiedGarbage.Impl.Aes.Arm.Linear

/-!
# The layers of bitsliced Camellia on ARMv7

Eight blocks at a time, on 32-bit planes, as SM4's (`Impl/Sm4/Arm/Layers.lean`):
each of the four big-endian 32-bit words of the eight blocks is eight
planes, bit `8 i + b` of plane `j` of word `w` being bit `j` of byte `i`
(from the most significant) of word `w` of block `b`. A 64-bit half
(`D1`: words 0 and 1, `D2`: words 2 and 3, RFC 3713 §2.3) is sixteen
planes: its left 32 bits (`t1 … t4`) in planes 0–7, its right 32 bits
(`t5 … t8`) in planes 8–15. A rotation of the half's left or right word by
8 bits is a rotation of each of its planes by 8.

So the P-function (§2.4.1) is, on each plane `j`, five XORs of the left
and right planes with each other rotated by 0, 8 or 16 bits; the 32-bit
rotation of FL and FLINV (§2.4.2) by one bit takes each plane to the next,
and plane 7 to plane 0 rotated by 8. `SBOX2`, `SBOX3` and `SBOX4` are
`SBOX1` with a rotation of the output or input byte, that is a renaming of
planes in the bytes that use them, which a masked exchange of neighbouring
planes makes. The S-box runs on the left word's eight planes, then on the
right word's.

The scratch buffer at `r8` holds, in 4-byte slots: all ones and the
S-box's spills (0–31); the left word's S-box output during a round
(32–39); the planes of `D1` (40–55) and `D2` (56–71); the table of the
bitsliced subkeys, sixteen planes each, in the order the rounds use them
(72–615); the addresses of the end of the current group's rounds (616) and
of the postwhitening's entry (617); the callee-saved registers `r4`–`r11`
and `lr` (618–626); the data pointer and the blocks left (627, 628); and
the tail buffer (632–663, eight blocks), through which every group is
copied. The modes keep their own state after it. The round key's entry is
at `kp` (`r9`).
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Aes.Arm

/-! ## Slots -/

/-- The left word's S-box output. -/
def ylSlot : Nat := 32
def d1Slot : Nat := 40
def d2Slot : Nat := 56
/-- Plane `j` of word `w` (0–3) of the state: `D1`'s words, then `D2`'s. -/
def stateSlot (w j : Nat) : Nat := d1Slot + 8 * w + j
def keySlot : Nat := 72
/-- After the table of 34 subkeys. -/
def grpSlot : Nat := keySlot + 16 * 34
def endSlot : Nat := grpSlot + 1
def savedSlot : Nat := endSlot + 1
def dSlot : Nat := savedSlot + 9
def nSlot : Nat := dSlot + 1
def tailSlot : Nat := 632
/-- Word `w` of block `b` of the tail buffer. -/
def tailAt (b w : Nat) : Nat := tailSlot + 4 * b + w

/-- The number of slots: the tail buffer's 32, then the modes' 16. -/
def slots : Nat := tailSlot + 48

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.r4, savedSlot), (.r5, savedSlot + 1), (.r6, savedSlot + 2), (.r7, savedSlot + 3), (.r8, savedSlot + 4),
   (.r9, savedSlot + 5), (.r10, savedSlot + 6), (.r11, savedSlot + 7), (.lr, savedSlot + 8)]

/-- Save and restore them, with the scratch buffer's base in `b`. -/
def saveRegs (b : Reg) : List Instr := savedRegs.map fun (r, k) => .str r b (4 * k)
def restoreRegs (b : Reg) : List Instr := savedRegs.map fun (r, k) => .ldr r b (4 * k)

/-! ## A round -/

/-- XOR the planes at word `off` of `kp` into the state, after loading the
state from slot `d`. -/
def loadKeyed (d off : Nat) : List Instr :=
  (List.range 8).flatMap fun j => [ldS (q j) (d + j), .ldr t0 kp (4 * (off + j)), eorR (q j) (q j) t0]

/-- In the byte of the mask `m`, plane `j` takes plane `j - 1` (cyclically):
the byte is rotated left by one bit. -/
def rotUp (m : BitVec 32) : List Instr :=
  [movR t1 (q 7)] ++
  ((List.range 7).reverse.flatMap fun i =>
    [eorR t0 (q (i + 1)) (q i), .dp .and t0 t0 (.imm m), eorR (q (i + 1)) (q (i + 1)) t0]) ++
  [eorR t0 (q 0) t1, .dp .and t0 t0 (.imm m), eorR (q 0) (q 0) t0]

/-- In the byte of the mask `m`, plane `j` takes plane `j + 1` (cyclically):
the byte is rotated right by one bit. -/
def rotDown (m : BitVec 32) : List Instr :=
  [movR t1 (q 0)] ++
  ((List.range 7).flatMap fun i =>
    [eorR t0 (q i) (q (i + 1)), .dp .and t0 t0 (.imm m), eorR (q i) (q i) t0]) ++
  [eorR t0 (q 7) t1, .dp .and t0 t0 (.imm m), eorR (q 7) (q 7) t0]

/-- The left word (`t1 … t4` in bytes 0–3): `SBOX4`'s input (`t4`) is
rotated; `SBOX2`'s (`t2`) and `SBOX3`'s (`t3`) outputs. -/
def inSelL : List Instr := rotUp 0xFF000000
def outSelL : List Instr := rotUp 0x0000FF00 ++ rotDown 0x00FF0000

/-- The right word (`t5 … t8`): `SBOX4`'s input (`t7`); `SBOX2`'s (`t5`)
and `SBOX3`'s (`t6`) outputs. -/
def inSelR : List Instr := rotUp 0x00FF0000
def outSelR : List Instr := rotUp 0x000000FF ++ rotDown 0x0000FF00

/-- The left word of the half at slot `src` with the subkey's left planes
(word `off` of `kp`), and its input selection. -/
def preL (off src : Nat) : List Instr := loadKeyed src off ++ inSelL

/-- The left word's output selection, its planes to slots 32–39, then the
right word with the subkey's right planes, and its input selection. -/
def midLR (off src : Nat) : List Instr :=
  outSelL ++ (List.range 8).map (fun j => stS (ylSlot + j) (q j)) ++ loadKeyed (src + 8) (off + 8) ++ inSelR

/-- Plane `j` of the P-function, from the left word's plane in slot
`32 + j` (into `t1`) and the right word's in `q j`, XORed into the half at
slot `dst`. -/
def pPlane (dst j : Nat) : List Instr :=
  [ldS t1 (ylSlot + j), eorR t1 t1 (q j), .dp .eor t1 t1 (rorOp (q j) 16), eorR (q j) (q j) t1,
   .dp .eor (q j) (q j) (rorOp t1 8), .dp .eor t1 t1 (rorOp (q j) 16),
   ldS t0 (dst + j), eorR t0 t0 t1, stS (dst + j) t0,
   ldS t0 (dst + 8 + j), eorR t0 t0 (q j), stS (dst + 8 + j) t0]

/-- The right word's output selection, the P-function, and the XOR into
the half at slot `dst`. -/
def postP (dst : Nat) : List Instr := outSelR ++ (List.range 8).flatMap (pPlane dst)

/-- A round: `D_dst ^= F(D_src, k)`, the subkey's planes at word `off` of `kp`. -/
def round (off src dst : Nat) : List Instr :=
  preL off src ++ sboxCode ++ midLR off src ++ sboxCode ++ postP dst

/-! ## FL and FLINV -/

/-- Load (or store) the left word's planes of the half at slot `d`. -/
def loadL (d : Nat) : List Instr := (List.range 8).map fun j => ldS (q j) (d + j)
def storeL (d : Nat) : List Instr := (List.range 8).map fun j => stS (d + j) (q j)

/-- Plane `j` of `x2 ^= (x1 & k1) <<< 1`: the right word's plane `j` (at
slot `d + 8 + j`) takes the AND of the left word's (in the state) and the
subkey's (word `off` of `kp`) plane `j - 1`, and plane 0 that of plane 7
rotated by a byte. -/
def flRotStep (d off j : Nat) : List Instr :=
  let i := (j + 7) % 8
  [.ldr t0 kp (4 * (off + i)), andR t0 t0 (q i), ldS t1 (d + 8 + j),
   .dp .eor t1 t1 (if j = 0 then rorOp t0 8 else .reg t0), stS (d + 8 + j) t1]

def flRot (d off : Nat) : List Instr := (List.range 8).flatMap (flRotStep d off)

/-- Plane `j` of `x1 ^= x2 | k2`: the left word's plane `j`, in the state. -/
def flOrStep (d off j : Nat) : List Instr :=
  [.ldr t0 kp (4 * (off + 8 + j)), ldS t1 (d + 8 + j), .dp .orr t0 t0 (.reg t1), eorR (q j) (q j) t0]

def flOr (d off : Nat) : List Instr := (List.range 8).flatMap (flOrStep d off)

/-- FL on the half at slot `d`, the subkey at word `off` of `kp`. -/
def flCode (d off : Nat) : List Instr := loadL d ++ flRot d off ++ flOr d off ++ storeL d

/-- FLINV on the half at slot `d`. -/
def flinvCode (d off : Nat) : List Instr := loadL d ++ flOr d off ++ flRot d off ++ storeL d

/-- FLINV on `D2` with the subkey at the entry after `kp`'s, FL on `D1` with
`kp`'s, and on to the next entries. -/
def flLayer : List Instr := flinvCode d2Slot 16 ++ flCode d1Slot 0 ++ [.dp .add kp kp (.imm 128)]

end VG.Impl.Camellia.Arm
