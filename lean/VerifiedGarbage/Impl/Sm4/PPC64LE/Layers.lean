module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Sbox
public import VerifiedGarbage.Impl.Sm4.Lin
public import VerifiedGarbage.Impl.Aes.PPC64LE.Linear

/-!
# The layers of bitsliced SM4 on PPC64LE

As on x86-64 (`Impl/Sm4/X86_64/Layers.lean`, which describes the
representation) and AArch64 (`Impl/Sm4/AArch64/Layers.lean`, which this
follows): sixteen blocks at a time, each of the four 32-bit words
`X₀ … X₃` of the blocks as eight 64-bit planes, the S-box as the circuit
`Circuit.sbox`, and `L` and `L'` as XORs of rotations of the planes by
multiples of 16 bits. PPC64LE has no memory operands for logic
instructions, so each operand in memory (a plane of the state, a round
key's plane, a mask) is loaded into a temporary first. The transposes and
their masks (in `m 1 … m 6`) are AES's (`Impl/Aes/PPC64LE/Linear.lean`).

The scratch buffer at `r8` holds, in 8-byte slots: the S-box's spills
(0–47), the masks of the round keys' planes (48–50), the planes of the
state's four words (64–95), the tail buffer (96–127, sixteen blocks), the
table of the 32 bitsliced round keys (128–383), and the callee-saved
registers `r14`–`r31` (384–401).
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE
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

/-- The number of slots. -/
def slots : Nat := tableEnd + 18

def keyMasks : List (Nat × BitVec 64) :=
  [(evenSlot, 0x00FF00FF00FF00FF), (oddSlot, 0xFF00FF00FF00FF00), (grpSlot, 0x0000FFFF0000FFFF)]

/-- Values to their slots, through `t0`. -/
def setSlots (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => imm64 t0 v ++ [stS k t0]

/-- The callee-saved registers the code uses, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.r14, savedSlot), (.r15, savedSlot + 1), (.r16, savedSlot + 2), (.r17, savedSlot + 3),
   (.r18, savedSlot + 4), (.r19, savedSlot + 5), (.r20, savedSlot + 6), (.r21, savedSlot + 7),
   (.r22, savedSlot + 8), (.r23, savedSlot + 9), (.r24, savedSlot + 10), (.r25, savedSlot + 11),
   (.r26, savedSlot + 12), (.r27, savedSlot + 13), (.r28, savedSlot + 14), (.r29, savedSlot + 15),
   (.r30, savedSlot + 16), (.r31, savedSlot + 17)]

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
def kr : Reg := .r10

/-- The S-box's input, `X_b ⊕ X_c ⊕ X_d ⊕ rk`, with the round key at
entry `e` of `kr`. -/
def preX (e b c d : Nat) : List Instr :=
  (List.range 8).flatMap fun j =>
    [ldS (q j) (stateSlot b j), ldS t0 (stateSlot c j), xorR (q j) (q j) t0, ldS t0 (stateSlot d j),
     xorR (q j) (q j) t0, .load .d t0 kr (8 * (8 * e + j)), xorR (q j) (q j) t0]

/-- Plane `j` of `L(B)`, with `B`'s planes in the state registers, XORed into
the state's word `a`: with `Qⱼ` the planes of `B ⋘ 2` (`Bⱼ₋₂`, or `Bⱼ₊₆`
rotated a byte, in `t2`), `Bⱼ ⊕ (Bⱼ ⋘ 24) ⊕ Qⱼ ⊕ (Qⱼ ⋘ 8) ⊕ (Qⱼ ⋘ 16)`. -/
def linStep (a j : Nat) : List Instr :=
  let p := if 2 ≤ j then q (j - 2) else t2
  (if 2 ≤ j then [] else [rorI t2 (q (j + 6)) 16]) ++
  [rorI t1 p 16, xorR t0 p t1, rorI t1 p 32, xorR t0 t0 t1, xorR t0 t0 (q j), rorI t1 (q j) 48,
   xorR t0 t0 t1, ldS t1 (stateSlot a j), xorR t0 t0 t1, stS (stateSlot a j) t0]

/-- `X_a ⊕= L(B)`. -/
def linL (a : Nat) : List Instr := (List.range 8).flatMap (linStep a)

/-- Plane `j` of `L'(B) = B ⊕ (B ⋘ 13) ⊕ (B ⋘ 23)` XORed into the state's
word `a`. -/
def keyLinStep (a j : Nat) : List Instr :=
  (if 5 ≤ j then [rorI t0 (q (j - 5)) 16] else [rorI t0 (q (j + 3)) 32]) ++
  [xorR t0 t0 (q j)] ++
  (if j = 7 then [rorI t1 (q 0) 32] else [rorI t1 (q (j + 1)) 48]) ++
  [xorR t0 t0 t1, ldS t1 (stateSlot a j), xorR t0 t0 t1, stS (stateSlot a j) t0]

/-- `X_a ⊕= L'(B)`. -/
def linK (a : Nat) : List Instr := (List.range 8).flatMap (keyLinStep a)

def lin : Lin → Nat → List Instr
  | .enc => linL
  | .key => linK

/-- A round: `X_a ⊕= T(X_b ⊕ X_c ⊕ X_d ⊕ rk)`, the round key at entry `e` of `kr`. -/
def round (l : Lin) (e a b c d : Nat) : List Instr := preX e b c d ++ sboxCode ++ lin l a

/-- Four rounds, whose new words replace `X₀ … X₃` in turn. -/
def rounds4 (l : Lin) : List Instr :=
  round l 0 0 1 2 3 ++ round l 1 1 2 3 0 ++ round l 2 2 3 0 1 ++ round l 3 3 0 1 2

/-! ## The round keys' planes -/

/-- The round key `2 m + h`, half `h` of the 64-bit word at `r3`, in the
low 32 bits of `t1` (the others zero). -/
def keyWord (h : Nat) : List Instr :=
  if h = 0 then [.load .d t1 .r3 0, .lis (m 5) 0xFFFF, .ori (m 5) (m 5) 0xFFFF, shrI (m 5) (m 5) 32,
    andR t1 t1 (m 5)]
  else [.load .d t1 .r3 0, shrI t1 t1 32]

/-- Its bytes spread to the 16-bit groups, in reverse (the word is
little-endian, the state's bytes big-endian): bits `16 i … 16 i + 7` of
`t1` are its byte `3 - i`, the others zero. The halves first, to bits
`0 … 15` and `32 … 47` (the group mask, in `m 1`), then each byte to its
group, through the masks of bytes `0` and `4` (`m 3`) and `2` and `6`
(`m 2`), made from the group mask and the even bytes' one. -/
def keySpread : List Instr :=
  [ldS (m 1) grpSlot, rorI t0 t1 48, xorR t1 t1 t0, andR t1 t1 (m 1),
   ldS (m 2) evenSlot, andR (m 3) (m 2) (m 1), rorI t2 (m 1) 16, andR (m 2) (m 2) t2,
   rorI t0 t1 16, andR t0 t0 (m 2), rorI t1 t1 40, andR t1 t1 (m 3), xorR t1 t1 t0]

/-- Plane `j`: bit `j` of each group of the spread word (bits `16 i`, the
mask in `m 4`), filled to its sixteen bits by doubling. -/
def keyPlane (j : Nat) : List Instr :=
  (if j = 0 then [andR (q 0) t1 (m 4)] else [rorI (q j) t1 j, andR (q j) (q j) (m 4)]) ++
  [rorI t0 (q j) 63, xorR (q j) (q j) t0, rorI t0 (q j) 62, xorR (q j) (q j) t0,
   rorI t0 (q j) 60, xorR (q j) (q j) t0, rorI t0 (q j) 56, xorR (q j) (q j) t0]

/-- The planes of round key `2 m + h`, from the word at `r3`, in `q 0 … q 7`. -/
def keyLoad (h : Nat) : List Instr :=
  keyWord h ++ keySpread ++
  [.li (m 4) 1, rorI t0 (m 4) 48, xorR (m 4) (m 4) t0, rorI t0 (m 4) 32, xorR (m 4) (m 4) t0] ++
  (List.range 8).flatMap keyPlane

/-- Store the planes to the entry at `kr`. -/
def keyStore : List Instr := (List.range 8).map fun j => .store .d (q j) kr (8 * j)

def keyOne (h : Nat) : List Instr := keyLoad h ++ keyStore

end VG.Impl.Sm4.PPC64LE
