module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# The DES round function on RISC-V, as a 64-lane table lookup

The eight S-boxes of a round are looked up at once, in the 64 bit lanes of a
word. Byte `b` of each word serves S-box `7 - b`, whose six input bits `x`
(`x₀` least significant, as `Spec.TripleDes.sBox` reads them) are E of R
XORed with the round key:

* `ePart` moves the six bits of E of R for each S-box into a byte of its
  own. `R` (the low half of `a2`, masked) is first copied into `z`: bit `0` of `z` is
  bit 31 of `R`, bits `1`–`32` are bits `0`–`31`, and bit 33 is bit 0, so
  that S-box `7 - b`'s bits are the six at `4 b` of `z`. Three doubling
  steps (`unpack`), each keeping one half of every field and moving the
  other half up, then move field `b` to byte `b`.
* `kPart` does the same with the round key (loaded from `a3` first), whose fields are
  already apart, at `6 b`; the steps' masks drop its upper sixteen bits.
* `maskPart` spreads bit `k` of each byte of their XOR to the whole byte, in
  `m k` (`s5`–`s10`).
* `treePart` runs a multiplexer tree on `m 0`–`m 4` whose 32 leaves are
  words of constants: lane `8 b + l` (`l < 8`) computes the table of output
  `laneOut b l` of S-box `7 - b`, for `x₅ = l / 4` (the other half's lanes
  are cleared by `m 5`).
* `pPart` then XORs the two halves of each byte, in its low four lanes, and
  moves each output bit to its destination under P in L (`a1`), in groups
  of the bits that move by the same distance (`pGroups`).

The words of constants (the tree's leaves, the steps' masks and P's) are
read from the frame at `sb` (`s4`), from byte `constOff` on, where `block`
stores them (`storeConsts`); they depend only on the S-boxes. The code
writes only temporaries, `a1` and `s5`–`s10`, and never memory: it has no
spills. It runs on all 64 lanes with no branches and no secret-dependent
addresses.
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64

/-- The frame's base, a multiple of 16. -/
def sb : Reg := .s4

/-- The word of the bits `f p` for `p < 64`. -/
def bitsOf (f : Nat → Bool) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 64).foldl (fun acc p => acc ||| (if f p then 2 ^ p else 0)) 0)

/-! ## The lanes -/

/-- The low lane of byte `b` that holds output `j` of S-box `7 - b`, chosen
so that P moves the outputs in few groups (`pGroups`). -/
def outLanes : List (List Nat) :=
  [[2, 1, 0, 3], [1, 2, 3, 0], [0, 1, 2, 3], [1, 3, 2, 0], [2, 1, 0, 3], [1, 0, 2, 3],
    [1, 2, 3, 0], [1, 0, 3, 2]]

def outLane (b j : Nat) : Nat := (outLanes.getD b []).getD j 0

/-- The output that lane `l` of byte `b` computes. -/
def laneOut (b l : Nat) : Nat := ((outLanes.getD b []).findIdx? (· == l % 4)).getD 0

/-- Lane `p`'s value on the six input bits `x`: its output of S-box
`7 - p / 8` when `x₅` is its half, and 0 otherwise. -/
def laneBit (p x : Nat) : Bool :=
  x / 32 == p % 8 / 4 &&
    (Spec.TripleDes.sBox (7 - p / 8) (BitVec.ofNat 6 x)).getLsbD (laneOut (p / 8) (p % 8))

/-- Leaf `n` of the tree: every lane's value on `x₀ … x₄ = n`. -/
def leaf (n : Nat) : BitVec 64 := bitsOf fun p => laneBit p (n + 32 * (p % 8 / 4))

/-! ## The words of constants -/

/-- Six bits at each multiple of 16. -/
def fields6 : BitVec 64 := 0x3F ||| 0x3F <<< 16 ||| 0x3F <<< 32 ||| 0x3F <<< 48

/-- The steps of `unpack` on E of R: the bits kept, the bits moved, and how far. -/
def eSteps : List (BitVec 64 × BitVec 64 × Nat) :=
  [(0x3FFFF, 0x3FFFF <<< 16, 16), (0x3FF ||| 0x3FF <<< 32, (0x3FF ||| 0x3FF <<< 32) <<< 8, 8),
    (fields6, fields6 <<< 4, 4)]

/-- The steps of `unpack` on the round key. -/
def kSteps : List (BitVec 64 × BitVec 64 × Nat) :=
  [(0xFFFFFF, 0xFFFFFF <<< 24, 8), (0xFFF ||| 0xFFF <<< 32, (0xFFF ||| 0xFFF <<< 32) <<< 12, 4),
    (fields6, fields6 <<< 6, 2)]

/-- The low bit of every byte. -/
def byteOnes : BitVec 64 := 0x0101010101010101

/-- The low word. -/
def lowWord : BitVec 64 := 0xFFFFFFFF

/-- The lanes of the half `x₅ = 0`. -/
def lowHalves : BitVec 64 := 0x0F0F0F0F0F0F0F0F

/-- P's moves: lane `8 b + outLane b j` (output `j` of S-box `7 - b`, bit
`4 b + j` of the substitution's output) goes to bit `31 - t` of L, where
`p[t] = 32 - (4 b + j)`. -/
def pMoves : List (Nat × Nat) :=
  (List.range 32).map fun t =>
    let src := 32 - Spec.TripleDes.p.getD t 1
    (8 * (src / 4) + outLane (src / 4) (src % 4), 31 - t)

/-- The distances of P's moves, in increasing order, without repetition. -/
def pDistances : List Int :=
  ((List.range 128).map fun (n : Nat) => (n : Int) - 64).filter fun d =>
    pMoves.any fun m => (m.2 : Int) - m.1 = d

/-- The lanes P moves by `d`. -/
def pGroup (d : Int) : List Nat := (pMoves.filter fun m => (m.2 : Int) - m.1 = d).map (·.1)

/-- The group's mask relative to its lowest lane `m`. -/
def pLow (d : Int) : Nat := ((pGroup d).foldl min 64)

def pRel (d : Int) : Nat := (pGroup d).foldl (fun acc a => acc ||| 2 ^ (a - pLow d)) 0

/-- Whether the group's mask, shifted down to its lowest lane, is an `andi` immediate. -/
def pSmall (d : Int) : Bool := pRel d < 2048

/-- The groups whose masks are words of constants. -/
def pLarge : List Int := pDistances.filter fun d => !pSmall d

def pMask (d : Int) : BitVec 64 := BitVec.ofNat 64 (pRel d) <<< pLow d

/-- The words of constants, in the order of their slots: the leaves of each
pair, `leaf (2 a)` and `leaf (2 a) ^^^ leaf (2 a + 1)`, then the steps'
masks, `byteOnes`, `lowHalves`, `lowWord` and P's masks. -/
def roundConsts : List (BitVec 64) :=
  ((List.range 16).flatMap fun a => [leaf (2 * a), leaf (2 * a) ^^^ leaf (2 * a + 1)]) ++
    ((eSteps ++ kSteps).flatMap fun st => [st.1, st.2.1]) ++ [byteOnes, lowHalves, lowWord] ++
    pLarge.map pMask

def leafSlot (a : Nat) : Nat := 2 * a
def diffSlot (a : Nat) : Nat := 2 * a + 1
def stepSlot (i : Nat) : Nat := 32 + 2 * i
def onesSlot : Nat := 44
def halvesSlot : Nat := 45
def lowSlot : Nat := 46
def pSlot (d : Int) : Nat := 47 + (pLarge.findIdx? (· == d)).getD 0

/-- The first byte of the words of constants in the frame (slot 15 on). -/
def constOff : Nat := 120

def ldc (d : Reg) (c : Nat) : Instr := .load .d d sb (constOff + 8 * c)

/-- Store the words `vs` at `off(sb)` on, through `t0` and `t1`. -/
def storeConsts : List (BitVec 64) → Nat → List Instr
  | [], _ => []
  | v :: vs, off =>
    Impl.Words.RISCV64.li64 .t0 .t1 v ++ ([.store .d .t0 sb off] : List Instr) ++
      storeConsts vs (off + 8)

/-! ## The code -/

/-- The input masks. -/
def m : Nat → Reg
  | 0 => .s5 | 1 => .s6 | 2 => .s7 | 3 => .s8 | 4 => .s9 | _ => .s10

/-- One doubling step on `y`, with the step's masks in slots `c` and `c + 1`. -/
def unpack (y : Reg) (c s : Nat) : List Instr :=
  [ldc .t1 c, .logic .and .t1 y .t1, ldc .t2 (c + 1), .logic .and .t2 y .t2,
    .shift .sll .d .t2 .t2 s, .logic .xor y .t1 .t2]

/-- E of R, a field in each byte of `t0`. -/
def ePart : List Instr :=
  [ldc .t0 lowSlot, .logic .and .t0 .a2 .t0, .shift .sll .d .t1 .t0 1, .shift .srl .d .t2 .t0 31,
    .logic .xor .t1 .t1 .t2, .shift .sll .d .t2 .t0 33, .logic .xor .t0 .t1 .t2] ++
    unpack .t0 (stepSlot 0) 16 ++ unpack .t0 (stepSlot 1) 8 ++ unpack .t0 (stepSlot 2) 4

/-- The round key, into `t4`. -/
def keyLoad : List Instr := [.load .d .t4 .a3 0]

/-- The round key in `t4`, a field in each byte. -/
def kPart : List Instr :=
  unpack .t4 (stepSlot 3) 8 ++ unpack .t4 (stepSlot 4) 4 ++ unpack .t4 (stepSlot 5) 2

/-- `m k`: bit `k` of each byte of `t0` spread to the byte. -/
def spread (k : Nat) : List Instr :=
  (if k = 0 then [.logic .and (m k) .t0 .t3]
    else [.shift .srl .d (m k) .t0 k, .logic .and (m k) (m k) .t3]) ++
  [.shift .sll .d .t1 (m k) 1, .logic .xor (m k) (m k) .t1,
    .shift .sll .d .t1 (m k) 2, .logic .xor (m k) (m k) .t1,
    .shift .sll .d .t1 (m k) 4, .logic .xor (m k) (m k) .t1]

/-- The S-boxes' inputs, and their bits spread. -/
def maskPart : List Instr :=
  [.logic .xor .t0 .t0 .t4, ldc .t3 onesSlot] ++ (List.range 6).flatMap spread

/-- The tree's node over `x₀ … x_{t-1}` for the leaves from `n` on, into
`dst`, with the registers `free` (at least `t` of them) for the others. -/
def tree : Nat → Nat → Reg → List Reg → List Instr
  | 0, _, _, _ => []
  | 1, n, dst, free =>
    let r := free.headD .t1
    [ldc dst (leafSlot (n / 2)), ldc r (diffSlot (n / 2)), .logic .and r r (m 0),
      .logic .xor dst dst r]
  | t + 2, n, dst, free =>
    let r := free.headD .t1
    tree (t + 1) n dst free ++ tree (t + 1) (n + 2 ^ (t + 1)) r free.tail ++
      [.logic .xor r dst r, .logic .and r r (m (t + 1)), .logic .xor dst dst r]

/-- The tables of the lanes' half, in `t0`. -/
def treePart : List Instr :=
  tree 5 0 .t0 [.t1, .t2, .t3, .t4, .t5] ++
    [ldc .t6 halvesSlot, .logic .xor .t6 (m 5) .t6, .logic .and .t0 .t0 .t6]

/-- Shift `r` left by `n`, or right by `-n`. -/
def shiftBy (r : Reg) (n : Int) : List Instr :=
  if 0 < n then [.shift .sll .d r r n.toNat]
  else if n < 0 then [.shift .srl .d r r (-n).toNat] else []

/-- The bits of the group at distance `d` into L. -/
def pGroupCode (d : Int) : List Instr :=
  (if pSmall d then
    (if pLow d = 0 then [] else [.shift .srl .d .t1 .t0 (pLow d)]) ++
      [.logicImm .and .t1 (if pLow d = 0 then .t0 else .t1) (pRel d)] ++ shiftBy .t1 (d + pLow d)
  else [ldc .t1 (pSlot d), .logic .and .t1 .t1 .t0] ++ shiftBy .t1 d) ++
  ([.logic .xor .a1 .a1 .t1] : List Instr)

/-- The outputs, from both halves of each byte, into L under P. -/
def pPart : List Instr :=
  [.shift .srl .d .t1 .t0 4, .logic .xor .t0 .t0 .t1] ++ pDistances.flatMap pGroupCode

/-- L XORed with the round function of R and the round key at `a3`. -/
def feistel : List Instr := keyLoad ++ (ePart ++ kPart ++ maskPart) ++ treePart ++ pPart

end VG.Impl.TripleDes.RISCV64
