module

public import VerifiedGarbage.Impl.Ed25519.Arm.FieldMemory
public import VerifiedGarbage.Impl.Ed25519.Arm.PointSelect
public import VerifiedGarbage.Impl.Ed25519.CombTable16

/-!
# Ed25519: base-point multiplication with a comb, one table per digit, on ARMv7

The scalar's 64 nibbles `n_i` give `[s]B = Σ d_i [16^i]B + [17 G]B` for the digits
`d_i = n_i - 8`, from `-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`. Table `i` holds
`[k]([16^i]B)` for `k = 1 … 8` (`combCached64`), affine and cached
(`[Y - X, Y + X, 2dT]`), each coordinate as the sixteen 16-bit limbs a field slot holds, so
that a selected entry is stored straight into slots 4–6: 1536 bytes a table, 96 KiB in all,
the static `combSym`. The accumulator, in slots 0–3, starts at `[17 G]B` (`combStart`), and
step `i` adds digit `i`'s entry of table `i`: 64 additions of affine cached points
(`addAffineOps`, seven multiplications each), and no doublings.

The digits are secret: their entries are selected in constant time. The scalar is first
copied into the workspace (`combCopy`), so that no step needs its address. Step `i` reads byte
`i / 2` of the copy and keeps its low or high nibble by a mask of the public `i`'s parity;
the masks of the eight magnitudes `k = 1 … 8` (all ones exactly for `|d| = k`) are in `r1`–`r8`,
and the sign's (all ones for a negative digit) at byte `SGN` of the workspace. Every word of
every candidate of table `i` is loaded, ANDed with its candidate's mask and ORed into `r9`,
at addresses from the static's and the loop's counter `r11`, which is public; `|d| = 0`
selects the identity's `[1, 1, 0]`. A negative digit's entry is then negated by exchanging
`Y - X` and `Y + X` and `2dT` with `0 - 2dT`, under the sign's mask.
-/

@[expose] public section

namespace VG.Impl.Ed25519.Arm

open VG.Arm

/-! ## The tables -/

/-- The static holding the comb's tables. -/
def combSym : String := "VG_ED25519_COMB"

/-- Coordinate `c` of a cached entry: `Y - X` (`c = 0`), `Y + X` (`c = 1`), `2dT` (`c = 2`). -/
def combCoord (p : Spec.Ed25519.Point) (c : Nat) : Spec.X25519.Fe :=
  if c = 0 then p.X else if c = 1 then p.Y else p.Z

/-- Limb `k` of coordinate `c` of entry `m + 1` of table `i`. -/
def combLimb (i m c k : Nat) : Nat := (combCoord (combCached64 i (m + 1)) c).val / 2 ^ (16 * k) % 2 ^ 16

/-- Word `q` (of 32 bits) of the tables: table `i = q / 384` takes 384 words, entry `m + 1`
of it 48 (`m = q % 384 / 48`), coordinate `c` 16 (`c = q % 48 / 16`), a limb a word. -/
def combLimbAt (q : Nat) : Nat := combLimb (q / 384) (q % 384 / 48) (q % 48 / 16) (q % 16)

/-- Word `j` (of 64 bits) of the tables: words `2 j` and `2 j + 1` of 32 bits. -/
def combWord (j : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (combLimbAt (2 * j) + 2 ^ 32 * combLimbAt (2 * j + 1))

/-- The words of the 64 tables, as the static `combSym` holds them. -/
def combWords : List (BitVec 64) := (List.range (64 * 192)).map combWord

/-- The static the comb reads. -/
def combConsts : List (String × List (BitVec 64)) := [(combSym, combWords)]

/-! ## The digits -/

/-- Byte of the workspace holding the scalar's copy (`combCopy`). -/
def SCAL : Nat := 2048

/-- Byte of the workspace holding the mask of the digit's sign. -/
def SGN : Nat := 56

/-- The registers of the masks of the magnitudes `1 … 8`. -/
def maskReg : Nat → Reg
  | 1 => .r1 | 2 => .r2 | 3 => .r3 | 4 => .r4 | 5 => .r5 | 6 => .r6 | 7 => .r7 | _ => .r8

/-- The mask of magnitude `k` into its register: all ones if `r10 = k`, else zero
(`r10 ⊕ k - 1` is negative exactly when `r10 = k`), with zero in `r9`. -/
def combMask (k : Nat) : List Instr :=
  [.dp .eor (maskReg k) .r10 (.imm (BitVec.ofNat 32 k)), .dp .sub (maskReg k) (maskReg k) (.imm 1),
    .mov (maskReg k) (.shifted (maskReg k) .lsr 31), .dp .sub (maskReg k) .r9 (.reg (maskReg k))]

/-- The scalar, at `r12`, copied to byte `SCAL` of the workspace, so that the steps read it
at addresses from `r0` alone. -/
def combCopy : List Instr :=
  (List.range 32).flatMap fun k => [.ldrb .r1 .r12 k, .strb .r1 .r0 (SCAL + k)]

/-- Digit `r11`: the nibble of byte `r11 / 2` of the scalar's copy (its high nibble for odd `r11`)
into `r4`, then its sign's mask to byte `SGN`, its magnitude into `r10`, and the masks of
the magnitudes into `r1`–`r8`; zero in `r9`. -/
def combDigit : List Instr :=
  [.dp .add .r12 .r0 (.imm (BitVec.ofNat 32 SCAL)), .mov .r2 (.shifted .r11 .lsr 1), .dp .add .r12 .r12 (.reg .r2),
    .ldrb .r3 .r12 0, .dp .and .r4 .r3 (.imm 15), .mov .r5 (.shifted .r3 .lsr 4),
    .mov .r9 (.imm 0), .dp .and .r6 .r11 (.imm 1), .dp .sub .r6 .r9 (.reg .r6),
    .dp .eor .r5 .r5 (.reg .r4), .dp .and .r5 .r5 (.reg .r6), .dp .eor .r4 .r4 (.reg .r5),
    .dp .sub .r4 .r4 (.imm 8), .mov .r5 (.shifted .r4 .lsr 31), .dp .sub .r5 .r9 (.reg .r5),
    .str .r5 .r0 SGN, .dp .eor .r10 .r4 (.reg .r5), .dp .sub .r10 .r10 (.reg .r5)] ++
  (List.range 8).flatMap fun k => combMask (k + 1)

/-! ## The selection -/

/-- `r12` = the address of table `r11`: the static's, plus 1536 bytes a table. -/
def tblAddr : List Instr :=
  [.adrSym .r12 combSym, .movw .r10 1536, .mul .r10 .r10 .r11, .dp .add .r12 .r12 (.reg .r10)]

/-- `r9` = `1` if every mask is clear (`|d| = 0`), else `0`. -/
def identityLimb : List Instr :=
  [.dp .orr .r9 .r1 (.reg .r2), .dp .orr .r9 .r9 (.reg .r3), .dp .orr .r9 .r9 (.reg .r4),
    .dp .orr .r9 .r9 (.reg .r5), .dp .orr .r9 .r9 (.reg .r6), .dp .orr .r9 .r9 (.reg .r7),
    .dp .orr .r9 .r9 (.reg .r8), .dp .and .r9 .r9 (.imm 1), .dp .eor .r9 .r9 (.imm 1)]

/-- Candidate `m + 1`'s limb at `r12 + d`, masked and ORed into `r9`. -/
def selectCand (d m : Nat) : List Instr :=
  [.ldr .r10 .r12 d, .dp .and .r10 .r10 (.reg (maskReg (m + 1))), .dp .orr .r9 .r9 (.reg .r10)]

/-- Limb `k` of coordinate `c` of the digit's entry into slot `4 + c`: the identity's limb
(`1` for limb 0 of `Y - X` and `Y + X`) where `|d| = 0`, else candidate `|d|`'s. -/
def selectLimb (c k : Nat) : List Instr :=
  (if c < 2 ∧ k = 0 then identityLimb else [.mov .r9 (.imm 0)]) ++
    (List.range 8).flatMap (fun m => selectCand (192 * m + 64 * c + 4 * k) m) ++
    [.str .r9 .r0 (64 + 64 * (4 + c) + 4 * k)]

/-- The digit's entry of table `r11` into slots 4–6, the identity's for `|d| = 0`. -/
def combSelect : List Instr :=
  tblAddr ++ (List.range 48).flatMap fun q => selectLimb (q / 16) (q % 16)

/-- The entry in slots 4–6 negated if the digit is negative: `Y - X` and `Y + X` exchanged,
and `2dT` with `0 - 2dT` (in slot 7, from the zero in slot 21), under the sign's mask. -/
def combNeg : Prog isa :=
  .seq (fieldCode [.sub 7 21 6]) (.block ([.ldr .r9 .r0 SGN] ++ swapFields [(4, 5), (6, 7)]))

/-! ## The addition -/

/-- Add the affine cached point in slots 4–6 (`[Y - X, Y + X, 2dT]` of a point with `Z = 1`)
to the point in slots 0–3, in place: `a = (Y₁ - X₁)(Y₂ - X₂)`, `b = (Y₁ + X₁)(Y₂ + X₂)`,
`c = T₁ 2dT₂`, `dd = 2 Z₁`, and `(b - a)(dd - c)`, `(dd + c)(b + a)`, `(dd - c)(dd + c)`,
`(b - a)(b + a)`: seven products, with slots 8–15 temporary. -/
def addAffineOps : List FieldOp := [
  .sub 8 1 0, .mul 8 8 4, .add 9 1 0, .mul 9 9 5, .mul 10 3 6, .add 11 2 2,
  .sub 12 9 8, .add 13 9 8, .sub 14 11 10, .add 15 11 10,
  .mul 0 12 14, .mul 1 15 13, .mul 2 14 15, .mul 3 12 13]

/-! ## The loop -/

/-- Step `r11 = i`: digit `i`'s entry of table `i`, negated for a negative digit, added to the
accumulator. Z is clear while another step follows. -/
def combStep : Prog isa :=
  .seq (.block (combDigit ++ combSelect)) <|
  .seq combNeg <|
  .seq (fieldCode addAffineOps) (.block [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 64)])

/-- `(x, y)` of `[17 G]B`. -/
def combStartAff : Spec.X25519.Fe × Spec.X25519.Fe :=
  (4650268310714759443145295274883477433952106455267492499975084996511359585556,
    4189685876054382644851338298926788466640410231895644581786650308218358658796)

/-- `[17 G]B`, with `Z = 1`: where the accumulator starts. -/
def combStart : Spec.Ed25519.Point :=
  ⟨combStartAff.1, combStartAff.2, 1, combStartAff.1 * combStartAff.2⟩

/-- The accumulator at `[17 G]B`, zero in slot 21, and the counter. -/
def combInit : Prog isa :=
  .seq (fieldCode ([.const 21 0] ++ constPointOps combStart)) (.block [.movw .r11 0])

/-- The scalar's copy, then the accumulator at `[17 G]B` and the counter. -/
def combPrepare : Prog isa := .seq (.block combCopy) combInit

/-- `[s]B` into slots 0–3, for the scalar at `r12`. -/
def combMultiply : Prog isa := .seq combPrepare (.loop combStep .ne)

end VG.Impl.Ed25519.Arm
