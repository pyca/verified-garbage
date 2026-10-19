module

public import VerifiedGarbage.Impl.Ed25519.CombTable16
public import VerifiedGarbage.Impl.Ed25519.AArch64.FieldMemory
public import VerifiedGarbage.Impl.X25519.AArch64.AltOps
import VerifiedGarbage.Impl.Ed25519.AArch64.Point64

/-!
# Ed25519: base-point multiplication with a comb, one table per digit

The scalar's 64 nibbles `n_i` (from its bits, expanded one per byte at byte
768 of the workspace) give `[s]B = Σ d_i [16^i]B + [17 G]B` for the digits
`d_i = n_i - 8`, from `-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`. Table `i`
holds `[k]([16^i]B)` for `k ≤ 8` (`combCached64`), affine; the 64 tables are
the static `combSym` (`combWords`, 768 bytes a table, 48 KiB). The
accumulator, in slots 0–3, starts at `[17 G]B` (`combStart`), and step `i`
adds digit `i`'s entry of table `i`: 64 additions of affine cached points,
inline on s2n-bignum's `_alt` field operations (`combAdd`, seven
multiplications), and no doublings.

The digits are secret: their entries are selected in constant time, as
s2n-bignum's `edwards25519_scalarmulbase_alt` selects (`combEntry`). Every
candidate of the table is loaded, a pair of words at a time, at addresses from
the static's and the loop's counter, and kept where the digit's magnitude is
its index (`csel`), from the identity's; then `2dT` is negated and `Y - X`,
`Y + X` exchanged under the sign's mask, in registers, and the entry stored
once. The loops' counter `x19`, which is also the table index, is public.
-/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

/-- `x2` = the nibble `b₀ + 2b₁ + 4b₂ + 8b₃` of the bits at `x8 + o`, by Horner's rule. -/
def combNibble (o : Nat) : List Instr :=
  [.ldrb .x2 .x8 (o + 3), .add .x .x2 .x2 .x2, .ldrb .x3 .x8 (o + 2), .add .x .x2 .x2 .x3,
    .add .x .x2 .x2 .x2, .ldrb .x3 .x8 (o + 1), .add .x .x2 .x2 .x3,
    .add .x .x2 .x2 .x2, .ldrb .x3 .x8 o, .add .x .x2 .x2 .x3]

/-- From the nibble `n` in `x2`: the sign's mask (all ones if `n < 8`) into `x1`, and
`|n - 8|` into `x2`. -/
def combSign : List Instr :=
  [.subImm .x .x3 .x2 8, .lsr .x .x1 .x3 63, .movz .w .x9 0 0, .sub .x .x1 .x9 .x1,
    .logic .eor .x .x2 .x3 .x1, .sub .x .x2 .x2 .x1]

/-- Word `w` of a field element. -/
def feWord (v : Spec.X25519.Fe) (w : Nat) : BitVec 64 := BitVec.ofNat 64 (v.val / 2 ^ (64 * w))

/-! ## The tables -/

/-- The static holding the comb's tables. -/
def combSym : String := "VG_ED25519_COMB"

/-- Word `i` of the tables: table `j = i / 96` takes 768 bytes, the `Y - X` (`c = 0`), the
`Y + X` (`c = 1`) and the `2dT` (`c = 2`) of its entries `m + 1 = 1 … 8`, four words each. -/
def combWord (i : Nat) : BitVec 64 :=
  let e := combCached64 (i / 96) (i % 32 / 4 + 1)
  feWord (if i % 96 < 32 then e.X else if i % 96 < 64 then e.Y else e.Z) (i % 4)

/-- The words of the 64 tables, as the static `combSym` holds them. -/
def combWords : List (BitVec 64) := (List.range (64 * 96)).map combWord

/-- The static the comb reads. -/
def combConsts : List (String × List (BitVec 64)) := [(combSym, combWords)]

/-- `x4`–`x7` where the sign's mask in `x1` is set, else `x12`–`x15`. -/
def negSel : List Instr :=
  [.tst .x .x1 .x1, .cselc .x .x4 .x4 .x12 .ne, .cselc .x .x5 .x5 .x13 .ne, .cselc .x .x6 .x6 .x14 .ne,
    .cselc .x .x7 .x7 .x15 .ne]

/-! ## The selection in registers

As s2n-bignum's `edwards25519_scalarmulbase_alt` selects: every candidate's words are loaded in
pairs (`ldp`) and kept where the digit's magnitude `|d|` (in `x2`) is the candidate's (`csel`),
starting from the identity's; then `2dT` is negated, `Y - X` and `Y + X` exchanged, for a
negative digit (the sign's mask in `x1`), and the entry stored to slots 4–6 once. -/

/-- Digit `x19`, whose bits are at `x0 + 768 + 4 x19`: its sign's mask to `x1` and its magnitude
to `x2`. -/
def combDigitS : List Instr :=
  [.lsl .x .x8 .x19 2, .add .x .x8 .x0 .x8] ++ combNibble 768 ++ combSign

/-- `x9` = the address of table `x19`, through `x16`. -/
def tblAddrS : List Instr :=
  [.adrSym .x9 combSym, .lsl .x .x16 .x19 8, .add .x .x9 .x9 .x16, .add .x .x9 .x9 .x16,
    .add .x .x9 .x9 .x16]

/-- The accumulators of the selection, in pairs, and their pairs' offsets in a table: `Y - X`
and `Y + X` (`scanAccs₁`, from `x9`), then `2dT` (`scanAccs₂`, from `x9 + 512`). -/
def scanAccs₁ : List (Reg × Reg × Nat) := [(.x3, .x4, 0), (.x5, .x6, 16), (.x7, .x8, 256), (.x10, .x11, 272)]
def scanAccs₂ : List (Reg × Reg × Nat) := [(.x12, .x13, 0), (.x14, .x15, 16)]

/-- The identity's cached form `[1, 1, 0]` in the accumulators. -/
def scanInit : List Instr :=
  [.movz .x .x3 1 0, .movz .x .x4 0 0, .movz .x .x5 0 0, .movz .x .x6 0 0,
    .movz .x .x7 1 0, .movz .x .x8 0 0, .movz .x .x10 0 0, .movz .x .x11 0 0,
    .movz .x .x12 0 0, .movz .x .x13 0 0, .movz .x .x14 0 0, .movz .x .x15 0 0]

/-- Candidate `m + 1`'s pairs at `x9 + o + 32 m`, kept in `accs` where `|d| = m + 1`. -/
def scanCand (accs : List (Reg × Reg × Nat)) (m : Nat) : List Instr :=
  [.movz .x .x16 (BitVec.ofNat 16 (m + 1)) 0, .subs .x .x16 .x2 .x16] ++
    accs.flatMap fun a => [.ldp .x16 .x17 .x9 (a.2.2 + 32 * m), .cselc .x a.1 .x16 a.1 .eq,
      .cselc .x a.2.1 .x17 a.2.1 .eq]

/-- `p - [x12–x15]` into `x20`–`x23`, from the constants `2⁶⁴ - 19`, `2⁶⁴ - 1`, `2⁶³ - 1`. -/
def scanNeg : List Instr :=
  [.movz .x .x17 0 0, .subImm .x .x17 .x17 1, .lsr .x .x24 .x17 1, .subImm .x .x16 .x17 18,
    .subs .x .x20 .x16 .x12, .sbcs .x .x21 .x17 .x13, .sbcs .x .x22 .x17 .x14, .sbc .x .x23 .x24 .x15]

/-- Under the sign's mask (`x1`): `2dT` negated, and `Y - X`, `Y + X` exchanged, stored to slots
4–6. -/
def scanSign : List Instr :=
  [.tst .x .x1 .x1,
    .cselc .x .x12 .x20 .x12 .ne, .cselc .x .x13 .x21 .x13 .ne,
    .cselc .x .x14 .x22 .x14 .ne, .cselc .x .x15 .x23 .x15 .ne,
    .cselc .x .x20 .x7 .x3 .ne, .cselc .x .x21 .x8 .x4 .ne,
    .cselc .x .x22 .x10 .x5 .ne, .cselc .x .x23 .x11 .x6 .ne,
    .cselc .x .x16 .x3 .x7 .ne, .cselc .x .x17 .x4 .x8 .ne,
    .cselc .x .x24 .x5 .x10 .ne, .cselc .x .x2 .x6 .x11 .ne,
    .stp .x20 .x21 .x0 (offset 4), .stp .x22 .x23 .x0 (offset 4 + 16),
    .stp .x16 .x17 .x0 (offset 5), .stp .x24 .x2 .x0 (offset 5 + 16),
    .stp .x12 .x13 .x0 (offset 6), .stp .x14 .x15 .x0 (offset 6 + 16)]

/-- The digit's entry from table `x19`, negated for a negative digit, to slots 4–6. -/
def combEntry : List Instr :=
  tblAddrS ++ scanInit ++ (List.range 8).flatMap (scanCand scanAccs₁) ++
    [.addImm .x .x9 .x9 512] ++ (List.range 8).flatMap (scanCand scanAccs₂) ++ scanNeg ++ scanSign

open VG.Impl.X25519.AArch64.Alt in
/-- The entry in slots 4–6 (`[Y - X, Y + X, 2dT]` of an affine point) added to the accumulator
in slots 0–3, in place, as s2n-bignum's `edwards25519_scalarmulbase_alt` does, operation for
operation: `addAffineOps`' formula on the `_alt` operations (`AltOps`), with slots 7–12
temporary and every coordinate of the accumulator below `2·p` between the additions. -/
def combAdd : List Instr :=
  [.movz .x .x17 0 0] ++
    addTwice4 (offset 7) (offset 2) (offset 2) ++ subTwice4 (offset 8) (offset 1) (offset 0) ++
    addTwice4 (offset 9) (offset 1) (offset 0) ++ mul4 (offset 10) (offset 3) (offset 6) ++
    mul4 (offset 8) (offset 8) (offset 4) ++ mul4 (offset 9) (offset 9) (offset 5) ++
    subTwice4 (offset 11) (offset 7) (offset 10) ++ addTwice4 (offset 7) (offset 7) (offset 10) ++
    subTwice4 (offset 12) (offset 9) (offset 8) ++ addTwice4 (offset 8) (offset 9) (offset 8) ++
    mul4 (offset 2) (offset 11) (offset 7) ++ mul4 (offset 0) (offset 12) (offset 11) ++
    mul4 (offset 1) (offset 7) (offset 8) ++ mul4 (offset 3) (offset 12) (offset 8)

/-- Step `x19 = i`: digit `i`'s entry of table `i`, negated for a negative digit, added to the
accumulator. `x8` is nonzero while another step follows. -/
def combStep : Prog isa :=
  .seq (.block combDigitS) <|
  .seq (.block combEntry) <|
  .seq (.block combAdd) (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 64])

/-- The steps from digit `j < 64` on. -/
def combLoopFrom (j : Nat) : Prog isa :=
  .seq (.block [.movz .w .x19 j 0]) (.loop combStep (.nonzero .x .x8))

/-- The 64 steps, one per digit. -/
def combLoop : Prog isa := combLoopFrom 0

/-- `(x, y)` of `[17 G]B`. -/
def combStartAff : Spec.X25519.Fe × Spec.X25519.Fe :=
  (4650268310714759443145295274883477433952106455267492499975084996511359585556,
    4189685876054382644851338298926788466640410231895644581786650308218358658796)

/-- `[17 G]B`, with `Z = 1`: where the accumulator starts. -/
def combStart : Spec.Ed25519.Point :=
  ⟨combStartAff.1, combStartAff.2, 1, combStartAff.1 * combStartAff.2⟩

/-- The accumulator at `[G']B`, and zero in slot 21. -/
def combInit : List Instr := fieldCode ([.const 21 0] ++ constPointOps combStart)

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768 onward. -/
def combMultiply : Prog isa :=
  .seq (.block combInit) combLoop

/-! ## Scalars whose bits 0–2 are clear

Digit 0 of such a scalar (X25519's, clamped) is `8 b₃ - 8`: `0` or `-8`. The
accumulator starts at `[17 G + d₀]B`, chosen between `[17 G]B` and `[17 G - 8]B`
by bit 3, so the loop starts at digit 1: 63 additions. -/

/-- `(x, y)` of `[17 G - 8]B`. -/
def combStart8Aff : Spec.X25519.Fe × Spec.X25519.Fe :=
  (3044058032842295632513412460065901946882459531655010849277392742361220705398,
    16382721024907912631339391052593996351625787231433860873492133196042675592609)

/-- `[17 G - 8]B`, with `Z = 1`. -/
def combStart8 : Spec.Ed25519.Point :=
  ⟨combStart8Aff.1, combStart8Aff.2, 1, combStart8Aff.1 * combStart8Aff.2⟩

/-- Slot `c` replaced by `v` where the mask in `x1` is set: `v` into `x4`–`x7`, `[c]` into
`x12`–`x15`, and the choice by `csel` stored back. -/
def constSel (c : Slot) (v : Spec.X25519.Fe) : List Instr :=
  constWords v ++ loads (offset c) .x12 .x13 .x14 .x15 ++ negSel ++ store4 (offset c)

/-- `x1` = the mask of bit 3 (at `x0 + 771`) being clear. -/
def clampMask : List Instr := [.ldrb .x2 .x0 771, .subImm .x .x1 .x2 1]

/-- The accumulator at `[17 G]B` for bit 3 set, else `[17 G - 8]B` (their `Z` is `1`), and
zero in slot 21. -/
def combInitClamped : List Instr :=
  combInit ++ clampMask ++ constSel 0 combStart8.X ++ constSel 1 combStart8.Y ++
    constSel 3 combStart8.T

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768 onward, bits 0–2 clear. -/
def combMultiplyClamped : Prog isa :=
  .seq (.block combInitClamped) (combLoopFrom 1)

end VG.Impl.Ed25519.AArch64
