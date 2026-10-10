import VerifiedGarbage.Impl.Sm4.AArch64.Sbox
import VerifiedGarbage.Impl.Sm4.Lin
import VerifiedGarbage.Impl.Aes.AArch64.Linear

/-!
# The layers of bitsliced SM4 on AArch64

As on x86-64 (`Impl/Sm4/X86_64/Layers.lean`, which describes the
representation): sixteen blocks at a time, each of the four 32-bit words
`X₀ … X₃` of the blocks as eight 64-bit planes, the S-box as the circuit
`Circuit.sbox`, and `L` and `L'` as XORs of rotations of the planes by
multiples of 16 bits. AArch64 has no memory operands for logic
instructions, so each operand in memory (a plane of the state, a round
key's plane, a mask) is loaded into a temporary first.

The scratch buffer at `x5` holds, in 8-byte slots: the S-box's spills
(0–47, also the masks of the transposes), the masks of the round keys'
planes (48–50), the planes of the state's four words (64–95), the tail
buffer (96–127, sixteen blocks), the table of the 32 bitsliced round keys
(128–383), and the callee-saved registers `x19`–`x28` (384–393). The modes
(`Impl/Modes/AArch64/`), which use slots 0–383 as SM4's core, keep their
own 12 slots after them (384–395): the callee-saved registers, then the
running counter.
-/

namespace VG.Impl.Sm4.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64
open VG.Impl.Sm4 (Lin)

/-! ## Slots -/

/-- The masks of the round keys' planes. -/
def evenSlot : Nat := 48
def oddSlot : Nat := 49
def grpSlot : Nat := 50

/-- Plane `j` of the state's word `w`. -/
def stateSlot (w j : Nat) : Nat := 64 + 8 * w + j

/-- Half `h` (bytes `8 h … 8 h + 7`) of block `b` of the tail buffer. -/
def tailSlot : Nat := 96
def tailAt (b h : Nat) : Nat := tailSlot + 2 * b + h

/-- The table of round keys, and its end. -/
def tableSlot : Nat := 128
def tableEnd : Nat := tableSlot + 8 * 32

def savedSlot : Nat := tableEnd

/-- The number of slots: ECB's, and the modes' 12 after the core's. -/
def slots : Nat := tableEnd + 12

def keyMasks : List (Nat × BitVec 64) :=
  [(evenSlot, 0x00FF00FF00FF00FF), (oddSlot, 0xFF00FF00FF00FF00), (grpSlot, 0x0000FFFF0000FFFF)]

/-- Values to their slots, through `t0`. -/
def setSlots (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => imm t0 v ++ [stS k t0]

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.x19, savedSlot), (.x20, savedSlot + 1), (.x21, savedSlot + 2), (.x22, savedSlot + 3),
   (.x23, savedSlot + 4), (.x24, savedSlot + 5), (.x25, savedSlot + 6), (.x26, savedSlot + 7),
   (.x27, savedSlot + 8), (.x28, savedSlot + 9)]

def saveRegs : List Instr := savedRegs.map fun (r, k) => stS k r
def restoreRegs : List Instr := savedRegs.map fun (r, k) => ldS r k

/-! ## Between blocks and planes -/

/-- Load the halves `h` of blocks `4 g … 4 g + 3` (to `q 0 … q 3`) and
`4 g + 8 … 4 g + 11` (to `q 4 … q 7`) from the tail buffer. -/
def loadPairs (g h : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [ldS (q k) (tailAt (4 * g + k) h), ldS (q (k + 4)) (tailAt (4 * g + k + 8) h)]

/-- Store them back. -/
def storePairs (g h : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [stS (tailAt (4 * g + k) h) (q k), stS (tailAt (4 * g + k + 8) h) (q (k + 4))]

/-- The tail buffer's slot of the interleaved word `w` of blocks `k` and `k + 8`. -/
def mixAt (w k : Nat) : Nat := tailAt (k + 8 * (w % 2)) (w / 2)

/-- In place in the tail buffer: the halves `h` of blocks `b` and `b + 8`,
for the four `b` of group `g`, become their words `2 h` and `2 h + 1`, each
with the bytes of the two blocks interleaved. -/
def mixIn (g h : Nat) : List Instr := loadPairs g h ++ zip1 ++ zip2 ++ swap8 ++ storePairs g h

/-- Back. -/
def mixOut (g h : Nat) : List Instr := loadPairs g h ++ swap8 ++ zip2 ++ zip1 ++ storePairs g h

/-- The interleaved words `w` of the eight pairs of blocks, transposed into
the state's word `d`. -/
def orthoIn (w d : Nat) : List Instr :=
  (List.range 8).map (fun k => ldS (q k) (mixAt w k)) ++ ortho ++
  (List.range 8).map (fun j => stS (stateSlot d j) (q j))

/-- The state's word `d`, transposed back into the interleaved words `w`. -/
def orthoOut (w d : Nat) : List Instr :=
  (List.range 8).map (fun j => ldS (q j) (stateSlot d j)) ++ ortho ++
  (List.range 8).map (fun k => stS (mixAt w k) (q k))

def mixes : List (Nat × Nat) := [(0, 0), (1, 0), (0, 1), (1, 1)]

/-- The sixteen blocks of the tail buffer to the planes of the state's
words, word `w` of the blocks to word `w` of the state. The tail buffer is
left holding the interleaved words. -/
def toBs : List Instr :=
  setMasks bsMasks ++ mixes.flatMap (fun (g, h) => mixIn g h) ++
  (List.range 4).flatMap fun w => orthoIn w w

/-- The planes back to the sixteen blocks in the tail buffer, the state's
words in reverse order (SM4's final reversal `R`): word `w` of the blocks
is word `3 - w` of the state, which is kept. -/
def fromBs : List Instr :=
  setMasks bsMasks ++ (List.range 4).flatMap (fun w => orthoOut w (3 - w)) ++
  mixes.flatMap fun (g, h) => mixOut g h

/-! ## A round -/

/-- The register of the round key's entry. -/
def kp : Reg := .x4

/-- The S-box's input, `X_b ⊕ X_c ⊕ X_d ⊕ rk`, with the round key at
entry `e` of `kp`. -/
def preX (e b c d : Nat) : List Instr :=
  (List.range 8).flatMap fun j =>
    [ldS (q j) (stateSlot b j), ldS t0 (stateSlot c j), eorR (q j) (q j) t0, ldS t0 (stateSlot d j),
     eorR (q j) (q j) t0, .ldr .x t0 kp (8 * (8 * e + j)), eorR (q j) (q j) t0]

/-- Plane `j` of `L(B)`, with `B`'s planes in the state registers, XORed into
the state's word `a`: with `Qⱼ` the planes of `B ⋘ 2` (`Bⱼ₋₂`, or `Bⱼ₊₆`
rotated a byte, in `t2`), `Bⱼ ⊕ (Bⱼ ⋘ 24) ⊕ Qⱼ ⊕ (Qⱼ ⋘ 8) ⊕ (Qⱼ ⋘ 16)`. -/
def linStep (a j : Nat) : List Instr :=
  let p := if 2 ≤ j then q (j - 2) else t2
  (if 2 ≤ j then [] else [rorI t2 (q (j + 6)) 16]) ++
  [rorI t1 p 16, eorR t0 p t1, rorI t1 p 32, eorR t0 t0 t1, eorR t0 t0 (q j), rorI t1 (q j) 48,
   eorR t0 t0 t1, ldS t1 (stateSlot a j), eorR t0 t0 t1, stS (stateSlot a j) t0]

/-- `X_a ⊕= L(B)`. -/
def linL (a : Nat) : List Instr := (List.range 8).flatMap (linStep a)

/-- Plane `j` of `L'(B) = B ⊕ (B ⋘ 13) ⊕ (B ⋘ 23)` XORed into the state's
word `a`. -/
def keyLinStep (a j : Nat) : List Instr :=
  (if 5 ≤ j then [rorI t0 (q (j - 5)) 16] else [rorI t0 (q (j + 3)) 32]) ++
  [eorR t0 t0 (q j)] ++
  (if j = 7 then [rorI t1 (q 0) 32] else [rorI t1 (q (j + 1)) 48]) ++
  [eorR t0 t0 t1, ldS t1 (stateSlot a j), eorR t0 t0 t1, stS (stateSlot a j) t0]

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

/-- Plane `j` of a round key's planes, from the planes of the eight copies of
the 64-bit word holding it (`h = 0`) and the next one (`h = 1`), in the
bytes of parity `h`: those bytes copied to the others, and the 16-bit groups
reversed (the word is little-endian, the state's bytes big-endian). -/
def keySel (h j : Nat) : List Instr :=
  (if h = 0 then [ldS t2 evenSlot, andR (q j) (q j) t2, rorI t0 (q j) 56]
   else [ldS t2 oddSlot, andR (q j) (q j) t2, rorI t0 (q j) 8]) ++
  [eorR (q j) (q j) t0, rorI (q j) (q j) 32, ldS t2 grpSlot] ++ swapIn (q j) t0 t2 16

/-- The planes of round key `2 m + h`, from the word at `x0`. -/
def keyLoad (h : Nat) : List Instr :=
  [.ldr .x (q 0) .x0 0] ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++
  setMasks bsMasks ++ zip1 ++ zip2 ++ ortho ++ (List.range 8).flatMap (keySel h)

/-- Store the planes to the entry at `kp`. -/
def keyStore : List Instr := (List.range 8).map fun j => .str .x (q j) kp (8 * j)

def keyOne (h : Nat) : List Instr := keyLoad h ++ keyStore

end VG.Impl.Sm4.AArch64
