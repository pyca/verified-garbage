module

public import VerifiedGarbage.Impl.Sm4.RISCV64.Sbox
public import VerifiedGarbage.Impl.Sm4.Lin
public import VerifiedGarbage.Impl.Aes.RISCV64.Linear
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# The layers of bitsliced SM4 on RISC-V

As on PPC64LE (`Impl/Sm4/PPC64LE/Layers.lean`, which this follows, and
x86-64, `Impl/Sm4/X86_64/Layers.lean`, which describes the representation):
sixteen blocks at a time, each of the four 32-bit words `X₀ … X₃` of the
blocks as eight 64-bit planes, the S-box as the circuit `Circuit.sbox`, and
`L` and `L'` as XORs of rotations of the planes by multiples of 16 bits.
The transpose of the bits (`ortho`) is AES's (`Impl/Aes/RISCV64/Linear.lean`),
as are the registers of its masks (`m 4 … m 6`) and of the masks of the
bytes' exchanges (`m 1 … m 3`). RV64I has no rotation: a rotation is a
right shift XORed with a left shift (`rorK`, through `a7`). RV64I builds
64-bit constants in several instructions, so the masks are set once, in
slots, and loaded from there (the linear layers' checks, which evaluate the
code, take them as known constants).

The scratch buffer at `a5` holds, in 8-byte slots: the S-box's spills
(0–39), the masks of the round keys' planes (40, 41), the transposes' masks
(45–50), the planes of the state's four words (64–95), the tail buffer
(96–127, sixteen blocks), the table of the 32 bitsliced round keys
(128–383), and the callee-saved registers `s0`–`s11` (384–395). The table
and the saved registers are beyond the reach of a load's offset from `a5`,
and are addressed through pointers to them.
-/

@[expose] public section

namespace VG.Impl.Sm4.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64
open VG.Impl.Sm4 (Lin)
open VG.Impl.Words.RISCV64 (li64)

/-! ## Slots -/

/-- The masks of the round keys' planes: of the two middle bytes of a round
key spread to the 16-bit groups, and of bit 0 of each group. -/
def midSlot : Nat := 40
def oneSlot : Nat := 41

/-- The transposes' masks `1 … 6`, in the slots from `bsBase` on. -/
def bsBase : Nat := 45

/-- Of them, the low word's and the one of the 16-bit groups 0 and 2. -/
def lowSlot : Nat := 45
def grpSlot : Nat := 46

/-- Plane `j` of the state's word `w`. -/
def stateSlot (w j : Nat) : Nat := 64 + 8 * w + j

/-- Half `h` (bytes `8 h … 8 h + 7`) of block `b` of the tail buffer. -/
def tailSlot : Nat := 96
def tailAt (b h : Nat) : Nat := tailSlot + 2 * b + h

/-- The table of round keys, and its end. -/
def tableSlot : Nat := 128
def tableEnd : Nat := tableSlot + 8 * 32

/-- The callee-saved registers' slots. -/
def savedSlot : Nat := tableEnd

/-- The number of slots. -/
def slots : Nat := savedSlot + 12

def keyMasks : List (Nat × BitVec 64) :=
  [(midSlot, 0x000000FF00FF0000), (oneSlot, 0x0001000100010001)]

/-- The transposes' masks: of the bytes' order (1–3) and `ortho`'s (4–6). -/
def bsKs : List (Nat × BitVec 64) :=
  [(lowSlot, 0x00000000FFFFFFFF), (grpSlot, 0x0000FFFF0000FFFF), (bsBase + 2, 0x00FF00FF00FF00FF),
   (bsBase + 3, 0x5555555555555555), (bsBase + 4, 0x3333333333333333), (bsBase + 5, 0x0F0F0F0F0F0F0F0F)]

/-- The transposes' masks to their registers. -/
def loadBsMasks : List Instr := (List.range 6).map fun k => ldS (m (k + 1)) (bsBase + k)

/-- Values to their slots, through `t0` and `t1`. -/
def setSlots (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => li64 t0 t1 v ++ [stS k t0]

/-- `r := ` the address of slot `k` (in two steps beyond an immediate's reach). -/
def slotAddr (r : Reg) (k : Nat) : List Instr :=
  if 8 * k < 2048 then [.addi r sb ((8 * k : Nat) : Int)]
  else [.addi r sb 2040, .addi r r ((8 * k - 2040 : Nat) : Int)]

/-- The callee-saved registers the code uses, and their offsets from the
first of their slots. -/
def savedOffs : List (Reg × Nat) :=
  [(.s0, 0), (.s1, 8), (.s2, 16), (.s3, 24), (.s4, 32), (.s5, 40), (.s6, 48), (.s7, 56),
   (.s8, 64), (.s9, 72), (.s10, 80), (.s11, 88)]

/-- The callee-saved registers to their slots, through `t0`. -/
def saveRegs : List Instr :=
  slotAddr t0 savedSlot ++ savedOffs.map fun (r, d) => .store .d r t0 d

/-- The callee-saved registers from their slots, through `t0`. -/
def restoreRegs : List Instr :=
  slotAddr t0 savedSlot ++ savedOffs.map fun (r, d) => .load .d r t0 d

/-- The rotation temporary. -/
def rk : Reg := .a7

/-- `d := n ⋙ k`, through `rk` (`n` and `d` are not `rk`). -/
def rorK (d n : Reg) (k : Nat) : List Instr := [shrI rk n k, shlI d n (64 - k), xorR d d rk]

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

/-- Exchanges between the words of blocks `k` (`q k`) and `k + 8`
(`q (k + 4)`): of index bit 3 (bytes), 4 (16-bit groups) or 5 (words) within
them, under the mask `i` (3, 2 or 1). -/
def pairSwap (i n : Nat) : List Instr :=
  (List.range 4).flatMap fun k => swapMove (q k) (q (k + 4)) t0 (m i) n

/-- In place in the tail buffer: the halves `h` of blocks `b` and `b + 8`,
for the four `b` of group `g`, become their words `2 h` and `2 h + 1`, each
with the bytes of the two blocks interleaved. -/
def mixIn (g h : Nat) : List Instr := loadPairs g h ++ pairSwap 3 8 ++ pairSwap 2 16 ++ pairSwap 1 32 ++ storePairs g h

/-- Back. -/
def mixOut (g h : Nat) : List Instr := loadPairs g h ++ pairSwap 1 32 ++ pairSwap 2 16 ++ pairSwap 3 8 ++ storePairs g h

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
  loadBsMasks ++ mixes.flatMap (fun (g, h) => mixIn g h) ++
  (List.range 4).flatMap fun w => orthoIn w w

/-- The planes back to the sixteen blocks in the tail buffer, the state's
words in reverse order (SM4's final reversal `R`): word `w` of the blocks
is word `3 - w` of the state, which is kept. -/
def fromBs : List Instr :=
  loadBsMasks ++ (List.range 4).flatMap (fun w => orthoOut w (3 - w)) ++
  mixes.flatMap fun (g, h) => mixOut g h

/-- Into `d`, through `tmp`: the state's word `w` of block 0, byte-reversed,
from its planes. Bit `16 i` of plane `j` (block 0) is bit `j` of the word's
byte `i` (from the most significant): the planes masked to those bits (by
`t3`) and shifted by `j` put byte `i` in bits `16 i … 16 i + 7`, and two
folds (the first masked by `t4`) put it in bits `8 i … 8 i + 7`. The bits
combined are disjoint, so XOR combines them. -/
def word0 (d tmp : Reg) (w : Nat) : List Instr :=
  [ldS d (stateSlot w 0), andR d d .t3] ++
  ((List.range 7).flatMap fun j =>
    [ldS tmp (stateSlot w (j + 1)), andR tmp tmp .t3, shlI tmp tmp (j + 1), xorR d d tmp]) ++
  [shrI tmp d 8, xorR d d tmp, andR d d .t4, shrI tmp d 16, xorR d d tmp]

/-- The tail buffer's word `h` of block 0, through `t0`–`t2` (and `t5`, the
low word's mask): the state's words `3 - 2 h` (low) and `2 - 2 h` (high)
of block 0, as `fromBs` leaves it. -/
def half0 (h : Nat) : List Instr :=
  word0 t2 t1 (2 - 2 * h) ++ [shlI t2 t2 32] ++ word0 t0 t1 (3 - 2 * h) ++
    [andR t0 t0 .t5, xorR t0 t0 t2, stS (tailAt 0 h) t0]

/-- Block 0 alone of `fromBs`: the tail buffer's first block from the
state's planes, with the masks of the bits of block 0 (`t3`), of the 16-bit
groups (`t4`) and of the low word (`t5`). -/
def fromBs0 : List Instr :=
  [ldS .t3 oneSlot, ldS .t4 grpSlot, ldS .t5 lowSlot] ++ half0 0 ++ half0 1

/-! ## A round -/

/-- The register of the round key's entry. -/
def kr : Reg := .a3

/-- The S-box's input, `X_b ⊕ X_c ⊕ X_d ⊕ rk`, with the round key at
entry `e` of `kr`. -/
def preX (e b c d : Nat) : List Instr :=
  (List.range 8).flatMap fun j =>
    [ldS (q j) (stateSlot b j), ldS t0 (stateSlot c j), xorR (q j) (q j) t0, ldS t0 (stateSlot d j),
     xorR (q j) (q j) t0, .load .d t0 kr (8 * (8 * e + j)), xorR (q j) (q j) t0]

/-- `X_a ⊕= L(B)`, with `B`'s planes in the state registers. With `ρ` the
rotation of the words by a byte and `V = B ⊕ ρ B`, `L(B)` is
`V_{j-2} ⊕ ρ²(B_{j-2} ⊕ ρ V_j)` for plane `j ≥ 2` and
`ρ V_{j+6} ⊕ ρ³(V_j ⊕ B_{j+6})` for `j < 2`. The planes are interleaved, so
that independent instructions are next to each other. -/
def linL (a : Nat) : List Instr := [
  shrI .t0 .s2 16, shlI .t1 .s2 48, ldS .t2 (stateSlot a 2), xorR .t0 .t0 .t1, shrI .t1 .s0 16, shlI
  .t3 .s0 48, shrI .t4 .s1 16, shlI .t5 .s1 48, xorR .t0 .s2 .t0, xorR .t1 .t1 .t3, xorR .t4 .t4
  .t5, shrI .t3 .s3 16, shrI .t5 .t0 16, shlI .t6 .t0 48, xorR .t1 .s0 .t1, shlI .a6 .s3 48, xorR
  .t4 .s1 .t4, xorR .t3 .t3 .a6, xorR .t5 .t5 .t6, xorR .t3 .s3 .t3, xorR .t5 .t5 .s0, ldS .s0
  (stateSlot a 3), shrI .t6 .t3 16, shlI .a6 .t3 48, xorR .t6 .t6 .a6, shrI .a6 .t5 32, xorR .t6 .t6
  .s1, shlI .t5 .t5 32, shrI .s1 .s4 16, xorR .a6 .a6 .t5, shlI .t5 .s4 48, xorR .a6 .a6 .t1, xorR
  .s1 .s1 .t5, shrI .t5 .t6 32, xorR .s1 .s4 .s1, shlI .t6 .t6 32, xorR .t5 .t5 .t6, xorR .a6 .a6
  .t2, shrI .t2 .s1 16, xorR .t5 .t5 .t4, stS (stateSlot a 2) .a6, shrI .t6 .s5 16, shlI .a6 .s5 48,
  xorR .t6 .t6 .a6, shlI .a6 .s1 48, xorR .t6 .s5 .t6, xorR .t2 .t2 .a6, ldS .a6 (stateSlot a 4),
  xorR .t2 .t2 .s2, xorR .t5 .t5 .s0, shrI .s0 .t6 16, shrI .s2 .t2 32, stS (stateSlot a 3) .t5,
  shlI .t5 .t6 48, shlI .t2 .t2 32, xorR .s0 .s0 .t5, ldS .t5 (stateSlot a 5), xorR .s2 .s2 .t2,
  shrI .t2 .s6 16, xorR .s0 .s0 .s3, shlI .s3 .s6 48, xorR .s2 .s2 .t0, xorR .t2 .t2 .s3, shrI .s3
  .s0 32, xorR .t2 .s6 .t2, shlI .s0 .s0 32, xorR .s3 .s3 .s0, xorR .s2 .s2 .a6, shrI .s0 .t2 16,
  xorR .s3 .s3 .t3, stS (stateSlot a 4) .s2, shrI .s2 .s7 16, shlI .t0 .s7 48, ldS .t3 (stateSlot a
  6), xorR .s2 .s2 .t0, shlI .t2 .t2 48, xorR .s2 .s7 .s2, xorR .s0 .s0 .t2, xorR .s4 .s0 .s4, xorR
  .s3 .s3 .t5, shrI .t0 .s2 16, shrI .t2 .s4 32, stS (stateSlot a 5) .s3, shlI .s2 .s2 48, shlI .s4
  .s4 32, ldS .s3 (stateSlot a 7), xorR .t0 .t0 .s2, xorR .t1 .t1 .s6, xorR .s5 .t0 .s5, xorR .t2
  .t2 .s4, shrI .s2 .s5 32, shlI .s5 .s5 32, shrI .s4 .t1 48, xorR .s2 .s2 .s5, xorR .t2 .t2 .s1,
  xorR .s2 .s2 .t6, shlI .t1 .t1 16, xorR .t2 .t2 .t3, xorR .s4 .s4 .t1, xorR .s2 .s2 .s3, stS
  (stateSlot a 6) .t2, xorR .t4 .t4 .s7, ldS .s1 (stateSlot a 0), xorR .s4 .s4 .s0, stS (stateSlot a
  7) .s2, shrI .s0 .t4 48, shlI .t4 .t4 16, ldS .s2 (stateSlot a 1), xorR .s0 .s0 .t4, xorR .s4 .s4
  .s1, xorR .s0 .s0 .t0, stS (stateSlot a 0) .s4, xorR .s0 .s0 .s2, stS (stateSlot a 1) .s0]

/-- Plane `j` of `L'(B) = B ⊕ (B ⋘ 13) ⊕ (B ⋘ 23)` XORed into the state's
word `a`. -/
def keyLinStep (a j : Nat) : List Instr :=
  (if 5 ≤ j then rorK t0 (q (j - 5)) 16 else rorK t0 (q (j + 3)) 32) ++
  [xorR t0 t0 (q j)] ++
  (if j = 7 then rorK t1 (q 0) 32 else rorK t1 (q (j + 1)) 48) ++
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

/-- The round key `2 m + h`, half `h` of the 64-bit word at `a0` (in the
schedule's copy in the working space), in the low 32 bits of `t1` (the
others zero). -/
def keyWord (h : Nat) : List Instr :=
  if h = 0 then [.load .d t1 .a0 0, ldS t2 lowSlot, andR t1 t1 t2]
  else [.load .d t1 .a0 0, shrI t1 t1 32]

/-- Its bytes spread to the 16-bit groups, in reverse (the word is
little-endian, the state's bytes big-endian): bits `16 i … 16 i + 7` of
`t1` are its byte `3 - i`; the bits above them in their groups, which
`keyBit` masks off, are any. Bytes 2 and 1 are where the groups 1 and 2 want
them in the word and in it shifted up by 24, bytes 3 and 0 where groups 0
and 3 do in it shifted down by 24 and up by 48. -/
def keySpread : List Instr :=
  [ldS t2 midSlot, shlI t0 t1 24, shlI .t3 t1 48, xorR t0 t0 t1, shrI .t4 t1 24, andR t0 t0 t2,
   xorR .t3 .t3 .t4, xorR t1 t0 .t3]

/-- Plane `j`, its bits at `16 i` only: bit `j` of each group of the spread
word (bits `16 i`, the mask in `m 4`, from `oneSlot`). The bits wanted
shift down to bit `0` of their groups and the others are masked off, so a
shift does what a rotation would. -/
def keyBit (j : Nat) : List Instr :=
  if j = 0 then [andR (q 0) t1 (m 4)] else [shrI (q j) t1 j, andR (q j) (q j) (m 4)]

/-- Each plane's bits filled to their sixteen bits: `x · 0xFFFF`, with no
carries between the groups. -/
def keyFill : List Instr :=
  [.lui t0 16, .addiw t0 t0 (-1)] ++ (List.range 8).map fun j => .mul (q j) (q j) t0

/-- The planes of round key `2 m + h`, from the word at `a0`, in `q 0 … q 7`,
before the fill. -/
def keyPre (h : Nat) : List Instr :=
  keyWord h ++ keySpread ++ ([ldS (m 4) oneSlot] : List Instr) ++ (List.range 8).flatMap keyBit

/-- The planes of round key `2 m + h`, from the word at `a0`, in `q 0 … q 7`. -/
def keyLoad (h : Nat) : List Instr := keyPre h ++ keyFill

/-- Store the planes to the entry at `kr`. -/
def keyStore : List Instr := (List.range 8).map fun j => .store .d (q j) kr (8 * j)

def keyOne (h : Nat) : List Instr := keyLoad h ++ keyStore

end VG.Impl.Sm4.RISCV64
