module

public import VerifiedGarbage.Impl.Ed25519.CombTable16
public import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Impl.Ed25519.AArch64.FieldMemory
public import VerifiedGarbage.Impl.Ed25519.AArch64.Point64
public import VerifiedGarbage.Impl.X25519.AArch64.AltOps

/-!
# Ed25519: base-point multiplication with a comb, one table per digit

The scalar's 64 nibbles `n_i` (from its bits, expanded one per byte at byte
768 of the workspace) give `[s]B = Σ d_i [16^i]B + [17 G]B` for the digits
`d_i = n_i - 8`, from `-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`. Table `i`
holds `[k]([16^i]B)` for `k ≤ 8` (`combCached64`), affine; the 64 tables are
the static `combSym` (`combWords`, 768 bytes a table, 48 KiB). The
accumulator, in slots 0–3, starts at `[17 G]B` (`combStart`), and step `i`
adds digit `i`'s entry of table `i`: 64 additions of affine cached points,
each a call of `vg_ed25519_r64_add_affine_ext` (seven multiplications), and
no doublings.

The digits are secret: their entries are selected in constant time. The
masks of the eight magnitudes `k = 1 … 8` (all ones exactly for `|d|`) and
the bit of `|d| = 0` stay in registers (`magRegs`, `x22`), and each mask is
copied into both lanes of a vector register (`maskV`). Each candidate is
loaded from the table 16 bytes at a time and inserted into `v2` where its
mask is set (BIT), on the vector pipes, which the additions leave idle:
every entry of the table is read, at addresses from the static's and the
loop's counter. Each entry is negated, or not, with the mask of its digit's
sign: its `Y - X` and `Y + X` are exchanged in the vector registers (BIT),
and its `2dT` chosen against its negation by `csel`. The loops' counter `x19`, which is
also the table index, is public.
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

/-- The registers holding the masks of the digit's magnitudes `1 … 8`. -/
def magRegs : List Reg := [.x12, .x13, .x14, .x15, .x16, .x17, .x20, .x21]

/-- Mask `k` of the digit. -/
def magReg (k : Nat) : Reg := magRegs.getD (k - 1) .x12

/-- `x22` = `[|d| < 1]` and `rs[k - 1]` = `[|d| < k]` for `k = 1 … 8`, then
`rs[k - 1]` = `[|d| < k] - [|d| < k + 1]`: all ones exactly if `|d| = k`, for `|d|` in `x2`. -/
def combMasks : List Instr :=
  [.subImm .x .x22 .x2 1, .lsr .x .x22 .x22 63] ++
    (List.range 8).flatMap (fun k =>
      [.subImm .x (magRegs.getD k .x1) .x2 (k + 1),
        .lsr .x (magRegs.getD k .x1) (magRegs.getD k .x1) 63]) ++
    (List.range 8).map fun k =>
      if k < 7 then .sub .x (magRegs.getD k .x1) (magRegs.getD k .x1) (magRegs.getD (k + 1) .x1)
      else .subImm .x (magRegs.getD k .x1) (magRegs.getD k .x1) 1

/-- Digit `x19`, whose bits are at `x0 + 768 + 4 x19`: its masks to `magRegs` and `x22`. -/
def combDigit : List Instr :=
  [.lsl .x .x8 .x19 2, .add .x .x8 .x0 .x8] ++ combNibble 768 ++ combSign ++ combMasks

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

/-- `x9` = the address of table `x19`: the static's, plus 768 bytes a table. -/
def tblAddr : List Instr :=
  [.adrSym .x9 combSym, .lsl .x .x2 .x19 8, .add .x .x9 .x9 .x2, .add .x .x9 .x9 .x2,
    .add .x .x9 .x9 .x2]

/-- The vector register holding, in both lanes, the mask of magnitude `k = 1 … 8`
(`v16`–`v23`). -/
def maskV (k : Nat) : VReg := [VReg.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23].getD (k - 1) .v16

/-- The vector register candidate `m + 1`'s half is loaded into (`v24`–`v29`, `v0`, `v1`). -/
def candV (m : Nat) : VReg := [VReg.v24, .v25, .v26, .v27, .v28, .v29, .v0, .v1].getD m .v24

/-- The masks of the eight magnitudes, each in both lanes of `maskV k`. -/
def selectMasks : List Instr :=
  (List.range 8).map fun k => .vop (.dup .d2 (maskV (k + 1)) (magReg (k + 1)))

/-- The start of half `h` of a coordinate's selection, in `acc`: words `2h` and `2h + 1` of the
identity's `Y - X` and `Y + X` (if `one`; `1` and `0` for `|d| = 0`, from `x22`) or zero. -/
def selectHalfStart (acc : VReg) (one : Bool) (h : Nat) : List Instr :=
  [.vop (.movi0 acc)] ++ if one && h == 0 then [.vop (.ins .d2 acc 0 .x22)] else []

/-- Candidate `m + 1`'s half `h` of coordinate `c` (at `x9 + 256 c + 32 m + 16 h`), inserted
into `acc` where its mask is set (BIT). -/
def selectHalfCand (acc : VReg) (c h m : Nat) : List Instr :=
  [.ldrq (candV m) .x9 (256 * c + 32 * m + 16 * h), .vop (.bsel .bit acc (candV m) (maskV (m + 1)))]

/-- Half `h` (words `2h`, `2h + 1`) of entry `|d|`'s coordinate `c`, into `acc`. -/
def selectAcc (acc : VReg) (one : Bool) (c h : Nat) : List Instr :=
  selectHalfStart acc one h ++ (List.range 8).flatMap (selectHalfCand acc c h)

/-- Half `h` of entry `|d|`'s coordinate `c`, to byte `o + 16 h`. -/
def selectHalf (one : Bool) (c o h : Nat) : List Instr :=
  selectAcc .v2 one c h ++ [.strq .v2 .x0 (o + 16 * h)]

/-- Coordinate `c` of entry `|d|`, to byte `o`. -/
def selectField (one : Bool) (c o : Nat) : List Instr :=
  (List.range 2).flatMap fun h => selectHalf one c o h

/-- `v30` = the sign's mask (`x1`) in both lanes. -/
def signV : List Instr := [.vop (.dup .d2 .v30 .x1)]

/-- Half `h` of the entry's `Y - X` and `Y + X`, into `v2` and `v3`, exchanged where the sign's
mask in `v30` is set (BIT, through `v4`), to slots 4 and 5. -/
def selectPairHalf (h : Nat) : List Instr :=
  selectAcc .v2 true 0 h ++ selectAcc .v3 true 1 h ++
    [.vop (.mov .v4 .v2), .vop (.bsel .bit .v2 .v3 .v30), .vop (.bsel .bit .v3 .v4 .v30),
      .strq .v2 .x0 (offset 4 + 16 * h), .strq .v3 .x0 (offset 5 + 16 * h)]

/-- The digit's entry from table `x19`, to slots 4–6, its `Y - X` and `Y + X` exchanged for a
negative digit (the sign's mask in `x1`): every candidate is loaded, 16 bytes at a time, and
inserted where its digit's mask is set, so only the digit's survives. -/
def combSelect : List Instr :=
  tblAddr ++ selectMasks ++ signV ++ selectPairHalf 0 ++ selectPairHalf 1 ++
    selectField false 2 (offset 6)

/-- `x4`–`x7` where the sign's mask in `x1` is set, else `x12`–`x15`. -/
def negSel : List Instr :=
  [.tst .x .x1 .x1, .cselc .x .x4 .x4 .x12 .ne, .cselc .x .x5 .x5 .x13 .ne, .cselc .x .x6 .x6 .x14 .ne,
    .cselc .x .x7 .x7 .x15 .ne]

/-- Slot `c` negated where the sign's mask in `x1` is set: `0 - [c]` (slot 21 holds zero) into
`x4`–`x7`, `[c]` into `x12`–`x15`, and the choice by `csel` stored back. -/
def combNeg (c : Slot) : List Instr :=
  [.movz .w .x10 0 0, .movz .w .x11 38 0] ++ fieldSubWords (offset 21) (offset c) ++ borrow38 ++
    [.sub .x .x4 .x4 .x8] ++ loads (offset c) .x12 .x13 .x14 .x15 ++ negSel ++ store4 (offset c)

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
  .seq (.block combDigit) <|
  .seq (.block (combSelect ++ combNeg 6)) <|
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
