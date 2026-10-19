module

public import VerifiedGarbage.Impl.Ed25519.BaseMultiples
public import VerifiedGarbage.Impl.Ed25519.AArch64.BaseMultiply
public import VerifiedGarbage.Impl.Ed25519.AArch64.FieldMemory
public import VerifiedGarbage.Impl.Ed25519.AArch64.PointMul

/-!
# Verification's equation with 4-bit windows

Verification may leak its inputs, so its scalars `S` and `k` are public. It
computes `[k]A - [S]B` with one chain of doublings (`dblOps`), four per 4-bit window
of the scalars, from the top: each window adds `[a]A` for `k`'s digit `a`
from a table of `[1]A … [15]A` built at run time (byte 5376, cached), and `[-b]B`
for `S`'s digit `b` from a table copied from the static `bSym` (`negBaseCached`,
byte 2048). A zero digit adds nothing. The digits are first split out of the
inputs with vector instructions (`nibbles`), one per byte of the workspace: `k`'s 128 at byte 768
and `S`'s 64 at byte 896, nibble `j` at offset `j`. A window is then one
iteration of a loop over the nibbles left (the counter at byte 56), from the
top: `k`'s 128, of which only the low 64 have a nibble of `S` beside them. The
leading zero nibbles of `k` above its low 64 are skipped (`skipZero`): before
them the sum is zero, which doubles to itself. The equation `[S]B = R + [k]A`
holds exactly when the result equals `-R`, which the projective comparison
`pointEqual` checks.
-/
@[expose] public section

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

/-- The point at byte `o` to slots 0–3. -/
def pointTableRead (o : Nat) : List Instr :=
  [.movz .w .x19 0 0] ++ tableAddr o ++ pointFromTable

/-- Doubles slots 0–3 in place with `dbl-2008-hwcd` (for `a = -1`): `A = X²`, `B = Y²`,
`C = 2Z²`, `E = 2XY`, `G = B - A`, `F = C - G`, `H = A + B`, and `X = EF`, `Y = GH`,
`Z = FG`, and `T = EH` if `t` (only an addition reads `T`). -/
def dblOps (t : Bool) : List FieldOp :=
  [.sqr 8 0, .sqr 9 1, .sqr 10 2, .add 10 10 10, .mul 11 0 1, .add 11 11 11,
    .sub 12 9 8, .sub 13 10 12, .add 14 8 9, .mul 0 11 13, .mul 1 12 14, .mul 2 13 12] ++
    if t then [.mul 3 11 14] else []

/-- Four doublings without `T`, with the counter `x1`, then the last one's `T = EH`, from
its `E` and `H`, which every doubling leaves in slots 11 and 14 (`dblOps true`). -/
def doubleWindow : Prog isa :=
  .seq (.block [.movz .w .x1 4 0]) (.seq
    (.loop (.block (fieldCode (dblOps false) ++ [.subImm .x .x1 .x1 1])) (.nonzero .x .x1))
    (.block (fieldCode [.mul 3 11 14])))

/-- `[Y - X, Y + X, 2dT, 2Z]` of the point in slots 17–20 into slots 0–3, with `d` in slot 16. -/
def cacheOps : List FieldOp := [.sub 0 18 17, .add 1 18 17, .add 2 20 20, .mul 2 2 16, .add 3 19 19]

/-- The point in slots 0–3, cached, to entry `x19` of the table at byte 5376; slots 0–3 are kept. -/
def storeCached : List Instr :=
  fieldCode (savePointOps ++ cacheOps) ++ tableAddr 5376 ++ pointToTable ++ restorePoint

/-- `A` from byte 7424 into slots 0–3, cached into the table's entry 0 and into slots 4–7. -/
def aTableInit : List Instr :=
  pointTableRead 7424 ++ ([.movz .w .x19 0 0] : List Instr) ++ storeCached ++ tableAddr 5376 ++
    pointFromTableQ ++ [.movz .w .x19 1 0]

/-- Entry `x19` = entry `x19 - 1` (in slots 0–3) + `A` (cached in slots 4–7), cached; `x8` is
nonzero while another entry follows. -/
def aTableBody : List Instr :=
  pointAddCached ++ storeCached ++ [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 15]

/-- Entries `j < 15` of the table at byte 5376 are cached `[j + 1]A`. -/
def aTable : Prog isa := .seq (.block aTableInit) (.loop (.block aTableBody) (.nonzero .x .x8))

/-- The static holding the cached `-[1]B … -[15]B` (`bWords`). -/
def bSym : String := "VG_ED25519_VERIFY_NEG_BASE"

/-- Coordinate `c` of a point: `X`, `Y`, `Z`, `T` for `c = 0, 1, 2, 3`. -/
def pointCoord (q : Spec.Ed25519.Point) : Nat → Spec.X25519.Fe
  | 0 => q.X
  | 1 => q.Y
  | 2 => q.Z
  | _ => q.T

/-- Word `i` of the static: word `i % 4` of coordinate `i / 4 % 4` of `negBaseCached (i / 16)`,
128 bytes an entry, as a table entry holds it. -/
def bWord (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((pointCoord (negBaseCached (i / 16)) (i / 4 % 4)).val / 2 ^ (64 * (i % 4)))

/-- The words of the 15 entries, as the static `bSym` holds them. -/
def bWords : List (BitVec 64) := (List.range 240).map bWord

/-- The static verification reads. -/
def bConsts : List (String × List (BitVec 64)) := [(bSym, bWords)]

/-- Coordinate `c` of the static's entry at `x9` to the table entry at `x8`. -/
def bCopyCoord (c : Nat) : List Instr :=
  [.ldr .x .x4 .x9 (32 * c), .ldr .x .x5 .x9 (32 * c + 8), .ldr .x .x6 .x9 (32 * c + 16),
    .ldr .x .x7 .x9 (32 * c + 24)] ++ tableWords (32 * c)

/-- The static's entry at `x9` to entry `x19` of the table at byte 2048; `x9` moves to the next
entry, and `x8` is nonzero while another entry follows. -/
def bTableBody : List Instr :=
  tableAddr 2048 ++ (List.range 4).flatMap bCopyCoord ++
    [.addImm .x .x9 .x9 128, .addImm .x .x19 .x19 1, .subImm .x .x8 .x19 15]

/-- Entries `j < 15` of the table at byte 2048 are cached `-[j + 1]B`, copied from the static. -/
def bTable : Prog isa :=
  .seq (.block [.adrSym .x9 bSym, .movz .w .x19 0 0]) (.loop (.block bTableBody) (.nonzero .x .x8))

/-- 16 bytes at `x2 + src` split into their nibbles at `x0 + dst`, the low nibble of each byte
first, with 15 in every byte of `v7`. -/
def nibBlock (src dst : Nat) : List Instr :=
  [.ldrq .v0 .x2 src, .vop (.shift .ushr .b16 .v1 .v0 4), .vop (.logic .and .v0 .v0 .v7),
    .vop (.perm .zip1 .b16 .v2 .v0 .v1), .vop (.perm .zip2 .b16 .v3 .v0 .v1),
    .strq .v2 .x0 dst, .strq .v3 .x0 (dst + 16)]

/-- `16 n` bytes at `x2 + src` split into their nibbles at `x0 + dst`. -/
def nibBlocks (src dst n : Nat) : List Instr :=
  (List.range n).flatMap fun q => nibBlock (src + 16 * q) (dst + 32 * q)

/-- 15 in every byte of `v7`, then the 64 bytes at `x2` split into their 128 nibbles at byte 768. -/
def kNibblesAt : List Instr := [.movz .w .x8 15 0, .vop (.dup .b16 .v7 .x8)] ++ nibBlocks 0 768 4

/-- `k`'s 64 bytes (its pointer at byte 7952) split into its 128 nibbles at byte 768. -/
def kNibbles : List Instr := [ld .x2 7952] ++ kNibblesAt

/-- `S`'s 32 bytes (byte 32 on of the signature, whose pointer is at byte 7944) split into its
64 nibbles at byte 896. -/
def sNibbles : List Instr := [ld .x2 7944] ++ nibBlocks 32 896 2

/-- The scalars' nibbles, one per byte: nibble `j` of `k` at byte `768 + j`, of `S` at
`896 + j`. -/
def nibbles : List Instr := kNibbles ++ sNibbles

/-- `x19` = the nibble at byte `o + counter`. -/
def digitAt (o : Nat) : List Instr := [ld .x8 56, .add .x .x8 .x0 .x8, .ldrb .x19 .x8 o]

/-- Add entry `x19 - 1` of the table at byte `o`, unless `x19` is zero. -/
def addDigit (o : Nat) (add : List Instr) : Prog isa :=
  .ite (.nonzero .x .x19)
    (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
    (.block [])

/-- `pointAddCached` but for `T`, when a doubling follows, which does not read it. -/
def pointAddCachedP : List Instr := fieldCode pointAddCachedOps.dropLast

/-- Four doublings, then `k`'s digit, added with `add`. -/
def windowWith (digit add : List Instr) : Prog isa :=
  .seq doubleWindow (.seq (.block digit) (addDigit 5376 add))

/-- A window of `k` alone. -/
def windowA (digit : List Instr) : Prog isa := windowWith digit pointAddCachedP

/-- A window of `k` and of `S`: `S`'s addition reads the `T` of `k`'s. -/
def windowAB (digitA digitB : List Instr) : Prog isa :=
  .seq (windowWith digitA pointAddCached) (.seq (.block digitB) (addDigit 2048 pointAddCachedP))

/-- `x19` = the counter less 64: nonzero while a nibble of `k` alone follows. -/
def aboveLow : List Instr := [ld .x19 56, .subImm .x .x19 .x19 64]

/-- A nibble of `k` alone (nibbles 127 down to 64). -/
def nibStepA : Prog isa :=
  .seq (.block batchBegin) (.seq (windowA (digitAt 768)) (.block aboveLow))

/-- A nibble of `k` and of `S` (nibbles 63 down to 0). -/
def nibStepAB : Prog isa :=
  .seq (.block batchBegin) (.seq (windowAB (digitAt 768) (digitAt 896)) (.block batchTest))

/-- `x19` = nibble `c - 1` of `k`, for the counter `c`, which is `x8 + 1`. -/
def skipLoad : List Instr :=
  [ld .x8 56, .subImm .x .x8 .x8 1, .add .x .x2 .x0 .x8, .ldrb .x19 .x2 768]

/-- Below a zero nibble, the counter moves down; `x19` is nonzero while another
nibble of `k` alone may be skipped. -/
def skipBody : Prog isa :=
  .seq (.block skipLoad) (.ite (.nonzero .x .x19) (.block [.movz .w .x19 0 0])
    (.block [st .x8 56, .subImm .x .x19 .x8 64]))

/-- Skip the leading zero nibbles of `k` above its low 64. -/
def skipZero : Prog isa := .loop skipBody (.nonzero .x .x19)

/-- The nibbles of `k` alone that are left after `skipZero`. -/
def windowsA : Prog isa :=
  .seq (.block aboveLow) (.ite (.nonzero .x .x19) (.loop nibStepA (.nonzero .x .x19)) (.block []))

/-- `-R` from byte 7552 into slots 4–7. -/
def negR : List Instr :=
  [.movz .w .x19 0 0] ++ tableAddr 7552 ++ pointFromTableQ ++ fieldCode [.const 8 0, .sub 4 8 4, .sub 7 8 7]

def windowSetup : List Instr := constField 16 Spec.Ed25519.d

def windowInit : List Instr := constPoint Spec.Ed25519.identity ++ mulCounterInit 128

end VG.Impl.Ed25519.AArch64
