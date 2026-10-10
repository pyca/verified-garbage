import VerifiedGarbage.Impl.Sm4.Arm.Sbox
import VerifiedGarbage.Impl.Sm4.Lin
import VerifiedGarbage.Impl.Aes.Arm.Linear

/-!
# The layers of bitsliced SM4 on ARMv7

Eight blocks at a time, on 32-bit planes. Each of the four 32-bit words
`X₀ … X₃` of the eight blocks is eight planes: bit `8 i + b` of plane `j`
of word `w` is bit `j` of byte `i` (from the most significant) of word `w`
of block `b`. So a rotation of the words by 8 bits is a rotation of the
planes by 8, and `L` and `L'` are, on each plane, XORs of rotations of the
planes by multiples of 8 bits (the second operand's rotation).

Loading word `w` of the eight blocks (little-endian, so byte `i` from the
most significant is at bits `8 i … 8 i + 7`) into `q 0 … q 7`, AES's
`ortho` (the 8×8 bit transpose in each byte position) gives its planes,
and back.

The scratch buffer at `r8` holds, in 4-byte slots: all ones and the
S-box's spills (0–31), the planes of the state's four words (32–63), the
tail buffer (64–95, eight blocks), the table of the 32 bitsliced round
keys, eight planes each, in the order the rounds use them (96–351), the
callee-saved registers `r4`–`r11` and `lr` (352–360), and the data
pointer and the blocks left (or the schedule's pointer) (361, 362). The
round key's entry is at `kp` (`r9`).
-/

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Aes.Arm
open VG.Impl.Sm4 (Lin)

/-! ## Slots -/

/-- Plane `j` of the state's word `w`. -/
def stateSlot (w j : Nat) : Nat := 32 + 8 * w + j

/-- Word `w` of block `b` of the tail buffer. -/
def tailSlot : Nat := 64
def tailAt (b w : Nat) : Nat := tailSlot + 4 * b + w

/-- The table of round keys, and its end. -/
def tableSlot : Nat := 96
def tableEnd : Nat := tableSlot + 8 * 32

def savedSlot : Nat := tableEnd
def dSlot : Nat := savedSlot + 9
def nSlot : Nat := dSlot + 1

/-- The number of slots. -/
def slots : Nat := nSlot + 1

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.r4, savedSlot), (.r5, savedSlot + 1), (.r6, savedSlot + 2), (.r7, savedSlot + 3), (.r8, savedSlot + 4),
   (.r9, savedSlot + 5), (.r10, savedSlot + 6), (.r11, savedSlot + 7), (.lr, savedSlot + 8)]

/-- Save and restore them, with the scratch buffer's base in `b`. -/
def saveRegs (b : Reg) : List Instr := savedRegs.map fun (r, k) => .str r b (4 * k)
def restoreRegs (b : Reg) : List Instr := savedRegs.map fun (r, k) => .ldr r b (4 * k)

/-! ## Between blocks and planes -/

/-- Word `w` of the eight blocks of the tail buffer to the planes of the
state's word `w`. -/
def toBsWord (w : Nat) : List Instr :=
  (List.range 8).map (fun b => ldS (q b) (tailAt b w)) ++ ortho ++
  (List.range 8).map (fun j => stS (stateSlot w j) (q j))

/-- The eight blocks of the tail buffer to the planes of the state's words. -/
def toBs : List Instr := (List.range 4).flatMap toBsWord

/-- The planes of the state's word `3 - w` to word `w` of the eight blocks
(SM4's final reversal `R`); the state is kept. -/
def fromBsWord (w : Nat) : List Instr :=
  (List.range 8).map (fun j => ldS (q j) (stateSlot (3 - w) j)) ++ ortho ++
  (List.range 8).map (fun b => stS (tailAt b w) (q b))

/-- The planes back to the eight blocks in the tail buffer. -/
def fromBs : List Instr := (List.range 4).flatMap fromBsWord

/-! ## A round -/

/-- The S-box's input, `X_b ⊕ X_c ⊕ X_d ⊕ rk`, with the round key at
entry `e` of `kp`. -/
def preX (e b c d : Nat) : List Instr :=
  (List.range 8).flatMap fun j =>
    [ldS (q j) (stateSlot b j), ldS t0 (stateSlot c j), eorR (q j) (q j) t0, ldS t0 (stateSlot d j),
     eorR (q j) (q j) t0, .ldr t0 kp (4 * (8 * e + j)), eorR (q j) (q j) t0]

/-- Plane `j` of `L(B)`, with `B`'s planes in the state registers, XORed into
the state's word `a`: with `Qⱼ` the planes of `B ⋘ 2` (`Bⱼ₋₂`, or `Bⱼ₊₆`
rotated a byte, in `u7`), `Bⱼ ⊕ (Bⱼ ⋘ 24) ⊕ Qⱼ ⊕ (Qⱼ ⋘ 8) ⊕ (Qⱼ ⋘ 16)`. -/
def linStep (a j : Nat) : List Instr :=
  let p := if 2 ≤ j then q (j - 2) else u7
  (if 2 ≤ j then [] else [.mov u7 (rorOp (q (j + 6)) 8)]) ++
  [.dp .eor t0 p (rorOp p 8), .dp .eor t0 t0 (rorOp p 16), eorR t0 t0 (q j), .dp .eor t0 t0 (rorOp (q j) 24),
   ldS t1 (stateSlot a j), eorR t0 t0 t1, stS (stateSlot a j) t0]

/-- `X_a ⊕= L(B)`. -/
def linL (a : Nat) : List Instr := (List.range 8).flatMap (linStep a)

/-- Plane `j` of `L'(B) = B ⊕ (B ⋘ 13) ⊕ (B ⋘ 23)` XORed into the state's
word `a`. -/
def keyLinStep (a j : Nat) : List Instr :=
  (if 5 ≤ j then [.dp .eor t0 (q j) (rorOp (q (j - 5)) 8)] else [.dp .eor t0 (q j) (rorOp (q (j + 3)) 16)]) ++
  (if j = 7 then [.dp .eor t0 t0 (rorOp (q 0) 16)] else [.dp .eor t0 t0 (rorOp (q (j + 1)) 24)]) ++
  [ldS t1 (stateSlot a j), eorR t0 t0 t1, stS (stateSlot a j) t0]

/-- `X_a ⊕= L'(B)`. -/
def linK (a : Nat) : List Instr := (List.range 8).flatMap (keyLinStep a)

def lin : Lin → Nat → List Instr
  | .enc => linL
  | .key => linK

/-- A round: `X_a ⊕= T(X_b ⊕ X_c ⊕ X_d ⊕ rk)`, the round key at entry `e` of `kp`. -/
def round (l : Lin) (e a b c d : Nat) : List Instr := preX e b c d ++ sboxCode ++ lin l a

/-- Four rounds, whose new words replace `X₀ … X₃` in turn. -/
def rounds4 (l : Lin) : List Instr :=
  round l 0 0 1 2 3 ++ round l 1 1 2 3 0 ++ round l 2 2 3 0 1 ++ round l 3 3 0 1 2

/-! ## The round keys' planes -/

/-- The round key at `r12`, its bytes reversed (the word's bytes are
little-endian, the state's from the most significant). -/
def keyWord : List Instr := [.ldr (q 0) .r12 0, .rev (q 0) (q 0)]

/-- Its planes: eight copies, transposed. -/
def keyPlanes : List Instr := ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ ortho

def keyLoad : List Instr := keyWord ++ keyPlanes

/-- Store the planes to the entry at `kp`. -/
def keyStore : List Instr := (List.range 8).map fun j => .str (q j) kp (4 * j)

def keyOne : List Instr := keyLoad ++ keyStore

end VG.Impl.Sm4.Arm
