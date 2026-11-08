module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Common

/-!
# The DES round function on PPC64LE, as a 64-lane table lookup

The round function of `Impl/TripleDes/RISCV64/Feistel.lean`, on PPC64LE: the
eight S-boxes of a round are looked up at once, in the 64 bit lanes of a
word. Byte `b` of each word serves S-box `7 - b`, whose six input bits `x`
(`x₀` least significant, as `Spec.TripleDes.sBox` reads them) are E of R
XORed with the round key:

* `ePart` moves the six bits of E of R for each S-box into a byte of its
  own. `R` (`r15`, masked to its low word) is first copied into `z`: bit `0`
  of `z` is bit 31 of `R`, bits `1`–`32` are bits `0`–`31`, and bits
  `33`–`63` are bits `0`–`30`, so that S-box `7 - b`'s bits are the six at
  `4 b` of `z`. Three doubling steps (`unpack`), each keeping one half of
  every field and moving the other half up, then move field `b` to byte `b`.
* `kPart` does the same with the round key (loaded from `r17` first), whose
  fields are already apart, at `6 b`; the steps' masks drop its upper
  sixteen bits.
* `maskPart` spreads bit `k` of each byte of their XOR to the whole byte, in
  `m k` (`r20`–`r25`).
* `treePart` runs a multiplexer tree on `m 0`–`m 4` whose 32 leaves are
  words of constants: lane `8 b + l` (`l < 8`) computes the table of output
  `laneOut b l` of S-box `7 - b`, for `x₅ = l / 4` (the other half's lanes
  are cleared by `m 5`).
* `pPart` then XORs the two halves of each byte, in its low four lanes, and
  moves each output bit to its destination under P in L (`r14`), in groups
  of the bits that move by the same distance (`pGroups`).

The PPC64LE model has no `andi`, and the evaluators of the proofs follow
no left shift of an unknown word, so a shift left by `n` is a rotation right
by `64 - n` of a word whose top `n` bits are zero; a group of one bit is
rotated to the top, shifted down to bit 0 alone and then up to its place;
and a group whose mask (shifted down to its lowest lane) is below `2 ^ 15`
gets it from `li`.

The other words of constants (the tree's leaves, the steps' masks and P's)
are read from the scratch buffer at `r5`, from slot 15 on (`constOff`),
where the block stores them (`storeConsts`); they depend only on the
S-boxes. The code writes only `r6`–`r12`, `r20`–`r25` and L, and never
memory: it has no spills. It runs on all 64 lanes with no branches and no
secret-dependent addresses.
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE

open VG.PPC64LE

/-- The scratch buffer's base. -/
def cb : Reg := .r5

/-- The temporaries. -/
def t0 : Reg := .r6
def t1 : Reg := .r7
def t2 : Reg := .r8
def t3 : Reg := .r9
def t4 : Reg := .r10
def t5 : Reg := .r11
def t6 : Reg := .r12

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

/-- A doubling step: the bits it keeps, `a`, and how far the bits `keep <<< a`
move up. -/
structure Step where
  keep : BitVec 64
  a : Nat
  s : Nat

/-- The steps of `unpack` on E of R. -/
def eSteps : List Step :=
  [⟨0x3FFFF, 16, 16⟩, ⟨0x3FF ||| 0x3FF <<< 32, 8, 8⟩, ⟨fields6, 4, 4⟩]

/-- The steps of `unpack` on the round key. -/
def kSteps : List Step :=
  [⟨0xFFFFFF, 24, 8⟩, ⟨0xFFF ||| 0xFFF <<< 32, 12, 4⟩, ⟨fields6, 6, 2⟩]

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

/-- The group's lowest lane, and its mask relative to it. -/
def pLow (d : Int) : Nat := ((pGroup d).foldl min 64)

def pRel (d : Int) : Nat := (pGroup d).foldl (fun acc a => acc ||| 2 ^ (a - pLow d)) 0

/-- Whether the group is one bit. -/
def pOne (d : Int) : Bool := (pGroup d).length == 1

/-- Whether the group's mask, shifted down to its lowest lane, is an `li` immediate. -/
def pSmall (d : Int) : Bool := pRel d < 2 ^ 15

/-- The groups whose masks are words of constants. -/
def pLarge : List Int := pDistances.filter fun d => !pOne d && !pSmall d

def pMask (d : Int) : BitVec 64 := BitVec.ofNat 64 (pRel d) <<< pLow d

/-- The words of constants, in the order of their slots: the leaves of each
pair, `leaf (2 a)` and `leaf (2 a) ^^^ leaf (2 a + 1)`, then the steps'
masks, `byteOnes`, `lowHalves`, `lowWord` and P's masks. -/
def roundConsts : List (BitVec 64) :=
  ((List.range 16).flatMap fun a => [leaf (2 * a), leaf (2 * a) ^^^ leaf (2 * a + 1)]) ++
    (eSteps ++ kSteps).map (·.keep) ++ [byteOnes, lowHalves, lowWord] ++ pLarge.map pMask

def leafSlot (a : Nat) : Nat := 2 * a
def diffSlot (a : Nat) : Nat := 2 * a + 1
def stepSlot (i : Nat) : Nat := 32 + i
def onesSlot : Nat := 38
def halvesSlot : Nat := 39
def lowSlot : Nat := 40
def pSlot (d : Int) : Nat := 41 + (pLarge.findIdx? (· == d)).getD 0

/-- The first byte of the words of constants in the scratch buffer (slot 15 on). -/
def constOff : Nat := 120

def ldc (d : Reg) (c : Nat) : Instr := .load .d d cb (constOff + 8 * c)

/-- `d := v` for a 64-bit constant: the high word with `lis` and `ori`,
shifted up by `sldi`, then the low word with `oris` and `ori`. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- Store the words `vs` at `off(cb)` on, through `r6`. -/
def storeConsts : List (BitVec 64) → Nat → List Instr
  | [], _ => []
  | v :: vs, off => movImm64 t0 v ++ ([.store .d t0 cb off] : List Instr) ++ storeConsts vs (off + 8)

/-! ## The code -/

/-- The input masks. -/
def m : Nat → Reg
  | 0 => .r20 | 1 => .r21 | 2 => .r22 | 3 => .r23 | 4 => .r24 | _ => .r25

/-- `d := n <<< k` for `0 < k < 64`, as a rotation, when the top `k` bits of
`n` are zero. -/
def shlRot (d n : Reg) (k : Nat) : Instr := .rotr .d d n (64 - k)

/-- One doubling step on `y`, with the step's mask in slot `c`: `y &&& keep`
and `(y &&& keep <<< a) <<< s`, as `((y >>> a) &&& keep) <<< (a + s)`. -/
def unpack (y : Reg) (c : Nat) (st : Step) : List Instr :=
  [ldc t1 c, .lsr .d t2 y st.a, .logic .and t2 t2 t1, .logic .and t1 y t1,
    shlRot t2 t2 (st.a + st.s), .logic .xor y t1 t2]

/-- E of R, a field in each byte of `t0`. -/
def ePart : List Instr :=
  [ldc t0 lowSlot, .logic .and t0 .r15 t0, .rotr .d t1 t0 63, .rotr .d t2 t0 31,
    .logic .xor t0 t1 t2] ++
    (List.range 3).flatMap fun i => unpack t0 (stepSlot i) (eSteps.getD i ⟨0, 1, 1⟩)

/-- The round key, into `t4`. -/
def keyLoad : List Instr := [.load .d t4 .r17 0]

/-- The round key in `t4`, a field in each byte. -/
def kPart : List Instr :=
  (List.range 3).flatMap fun i => unpack t4 (stepSlot (3 + i)) (kSteps.getD i ⟨0, 1, 1⟩)

/-- `m k`: bit `k` of each byte of `t0` spread to the byte. -/
def spread (k : Nat) : List Instr :=
  (if k = 0 then [.logic .and (m k) t0 t3]
    else [.lsr .d (m k) t0 k, .logic .and (m k) (m k) t3]) ++
  [shlRot t1 (m k) 1, .logic .xor (m k) (m k) t1,
    shlRot t1 (m k) 2, .logic .xor (m k) (m k) t1,
    shlRot t1 (m k) 4, .logic .xor (m k) (m k) t1]

/-- The S-boxes' inputs, and their bits spread. -/
def maskPart : List Instr :=
  [.logic .xor t0 t0 t4, ldc t3 onesSlot] ++ (List.range 6).flatMap spread

/-- The tree's node over `x₀ … x_{t-1}` for the leaves from `n` on, into
`dst`, with the registers `free` (at least `t` of them) for the others. -/
def tree : Nat → Nat → Reg → List Reg → List Instr
  | 0, _, _, _ => []
  | 1, n, dst, free =>
    let r := free.headD t1
    [ldc dst (leafSlot (n / 2)), ldc r (diffSlot (n / 2)), .logic .and r r (m 0),
      .logic .xor dst dst r]
  | t + 2, n, dst, free =>
    let r := free.headD t1
    tree (t + 1) n dst free ++ tree (t + 1) (n + 2 ^ (t + 1)) r free.tail ++
      [.logic .xor r dst r, .logic .and r r (m (t + 1)), .logic .xor dst dst r]

/-- The tables of the lanes' half, in `t0`. -/
def treePart : List Instr :=
  tree 5 0 t0 [t1, t2, t3, t4, t5] ++
    [ldc t6 halvesSlot, .logic .xor t6 (m 5) t6, .logic .and t0 t0 t6]

/-- Shift `r` left by `n`, or right by `-n`. -/
def shiftBy (r : Reg) (n : Int) : List Instr :=
  if 0 < n then [shlRot r r n.toNat]
  else if n < 0 then [.lsr .d r r (-n).toNat] else []

/-- The bits of the group at distance `d` into L. -/
def pGroupCode (d : Int) : List Instr :=
  (if pOne d then
    -- Lane `a` to bit 63, alone to bit 0, then up to bit `a + d`.
    [.rotr .d t1 t0 (pLow d + 1), .lsr .d t1 t1 63] ++ shiftBy t1 (pLow d + d)
  else if pSmall d then
    (if pLow d = 0 then [] else [.lsr .d t1 t0 (pLow d)]) ++
      [.li t2 (pRel d), .logic .and t1 (if pLow d = 0 then t0 else t1) t2] ++
      shiftBy t1 (d + pLow d)
  else [ldc t1 (pSlot d), .logic .and t1 t1 t0] ++ shiftBy t1 d) ++
  ([.logic .xor .r14 .r14 t1] : List Instr)

/-- The outputs, from both halves of each byte, into L under P. -/
def pPart : List Instr :=
  [.lsr .d t1 t0 4, .logic .xor t0 t0 t1] ++ pDistances.flatMap pGroupCode

/-- L XORed with the round function of R and the round key at `r17`. -/
def feistel : List Instr := keyLoad ++ (ePart ++ kPart ++ maskPart) ++ treePart ++ pPart


end VG.Impl.TripleDes.PPC64LE
