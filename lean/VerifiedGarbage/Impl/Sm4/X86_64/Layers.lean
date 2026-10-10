import VerifiedGarbage.Impl.Sm4.X86_64.Sbox
import VerifiedGarbage.Impl.Sm4.Lin
import VerifiedGarbage.Impl.Aes.X86_64.Linear
import VerifiedGarbage.Impl.Aes.X86_64.Ctr32

/-!
# The layers of bitsliced SM4 on x86-64

Sixteen blocks at a time. Each of the four 32-bit words `X₀ … X₃` of the
sixteen blocks is eight 64-bit words, *planes*: bit `16 i + b` of plane `j`
of word `w` is bit `j` of byte `i` (from the most significant) of word `w`
of block `b`. So a rotation of the words by 8 bits is a rotation of the
planes by 16, and the round's linear transformations `L` and `L'` are, on
each plane, XORs of rotations of the planes by multiples of 16 bits.

The blocks are moved between the tail buffer, where `ecb` copies them, and
the planes by AES's transposes: `zip1`, `zip2` and `swap8` interleave the
words of two blocks' halves, and `ortho` transposes the 8×8 bit matrices.

The scratch buffer at `r9` holds, in 8-byte slots: all ones (slot 0, for the
S-box), the S-box's spills (1–47, also the masks of the transposes), the
masks of the round keys' planes (48–50), the planes of the state's four
words (64–95), the tail buffer (96–127, sixteen blocks), the table of the
32 bitsliced round keys, eight planes each, in the order the rounds use
them (128–383), the callee-saved registers (384–389) and CTR's running counter block
(390–391).
-/

namespace VG.Impl.Sm4.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64
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

/-- The running counter block of CTR (`Ctr.lean`): its high and low halves,
as integers. -/
def ctrHi : Nat := savedSlot + 6
def ctrLo : Nat := savedSlot + 7

/-- The number of slots. -/
def slots : Nat := savedSlot + 8

def keyMasks : List (Nat × BitVec 64) :=
  [(evenSlot, 0x00FF00FF00FF00FF), (oddSlot, 0xFF00FF00FF00FF00), (grpSlot, 0x0000FFFF0000FFFF)]

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.rbx, savedSlot), (.rbp, savedSlot + 1), (.r12, savedSlot + 2), (.r13, savedSlot + 3),
   (.r14, savedSlot + 4), (.r15, savedSlot + 5)]

def saveRegs : List Instr := savedRegs.map fun (r, k) => st k r
def restoreRegs : List Instr := savedRegs.map fun (r, k) => movS r k

/-! ## Between blocks and planes -/

/-- Load the halves `h` of blocks `4 g … 4 g + 3` (to `q 0 … q 3`) and
`4 g + 8 … 4 g + 11` (to `q 4 … q 7`) from the tail buffer. -/
def loadPairs (g h : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [movS (q k) (tailAt (4 * g + k) h), movS (q (k + 4)) (tailAt (4 * g + k + 8) h)]

/-- Store them back. -/
def storePairs (g h : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [st (tailAt (4 * g + k) h) (q k), st (tailAt (4 * g + k + 8) h) (q (k + 4))]

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
  (List.range 8).map (fun k => movS (q k) (mixAt w k)) ++ ortho ++
  (List.range 8).map (fun j => st (stateSlot d j) (q j))

/-- The state's word `d`, transposed back into the interleaved words `w`. -/
def orthoOut (w d : Nat) : List Instr :=
  (List.range 8).map (fun j => movS (q j) (stateSlot d j)) ++ ortho ++
  (List.range 8).map (fun k => st (mixAt w k) (q k))

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
def kp : Reg := .rsi

/-- The memory operand of word `k` of the entries at `kp`. -/
def keyAt (k : Nat) : MemOp := slotAt kp k

/-- The S-box's input, `X_b ⊕ X_c ⊕ X_d ⊕ rk`, with the round key at
entry `e` of `kp`. -/
def preX (e b c d : Nat) : List Instr :=
  (List.range 8).flatMap fun j =>
    [movS (q j) (stateSlot b j), xorS (q j) (stateSlot c j), xorS (q j) (stateSlot d j),
     .alu .xor (q j) (.mem (keyAt (8 * e + j)))]

/-- Plane `j` of `L(B)`, with `B`'s planes in the state registers, XORed into
the state's word `a`: with `Qⱼ` the planes of `B ⋘ 2` (`Bⱼ₋₂`, or `Bⱼ₊₆`
rotated a byte), `Bⱼ ⊕ (Bⱼ ⋘ 24) ⊕ Qⱼ ⊕ (Qⱼ ⋘ 8) ⊕ (Qⱼ ⋘ 16)`. -/
def linStep (a j : Nat) : List Instr :=
  (if 2 ≤ j then [movR t0 (q (j - 2))] else [movR t0 (q (j + 6)), rorI t0 16]) ++
  [movR t1 t0, rorI t1 16, xorR t0 t1, rorI t1 16, xorR t0 t1, xorR t0 (q j), movR t1 (q j),
   rorI t1 48, xorR t0 t1, xorS t0 (stateSlot a j), st (stateSlot a j) t0]

/-- `X_a ⊕= L(B)`. -/
def linL (a : Nat) : List Instr := (List.range 8).flatMap (linStep a)

/-- Plane `j` of `L'(B) = B ⊕ (B ⋘ 13) ⊕ (B ⋘ 23)` XORed into the state's
word `a`. -/
def keyLinStep (a j : Nat) : List Instr :=
  [movR t0 (q j)] ++
  (if 5 ≤ j then [movR t1 (q (j - 5)), rorI t1 16] else [movR t1 (q (j + 3)), rorI t1 32]) ++
  [xorR t0 t1] ++
  (if j = 7 then [movR t1 (q 0), rorI t1 32] else [movR t1 (q (j + 1)), rorI t1 48]) ++
  [xorR t0 t1, xorS t0 (stateSlot a j), st (stateSlot a j) t0]

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
  (if h = 0 then [andS (q j) evenSlot, movR t0 (q j), rorI t0 56]
   else [andS (q j) oddSlot, movR t0 (q j), rorI t0 8]) ++
  [xorR (q j) t0, rorI (q j) 32] ++ swapIn (q j) t0 grpSlot 16

/-- The planes of round key `2 m + h`, from the word at `rdi`. -/
def keyLoad (h : Nat) : List Instr :=
  [.mov (q 0) (.mem (at_ .rdi 0))] ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++
  setMasks bsMasks ++ zip1 ++ zip2 ++ ortho ++ (List.range 8).flatMap (keySel h)

/-- Store the planes to the entry at `rsi`. -/
def keyStore : List Instr := (List.range 8).map fun j => .store (slotAt .rsi j) (q j)

def keyOne (h : Nat) : List Instr := keyLoad h ++ keyStore

end VG.Impl.Sm4.X86_64
