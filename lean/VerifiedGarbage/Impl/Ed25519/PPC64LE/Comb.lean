module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.FieldMemory
public import VerifiedGarbage.Impl.Ed25519.CombTable16

/-!
# Ed25519: base-point multiplication with a comb, one table per digit, on PPC64LE

RISC-V's comb (`Impl/Ed25519/RISCV64/Comb.lean`) on PPC64LE's field code. The scalar's 64
nibbles `n_i` give `[s]B = Σ d_i [16^i]B + [17 G]B` for the digits `d_i = n_i - 8`, from
`-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`. Table `i` holds `[k]([16^i]B)` for `k = 1 … 8`
(`combCached64`), affine and cached (`[Y - X, Y + X, 2dT]`), each coordinate as the eight
32-bit limbs a field slot holds, so that a selected entry is stored straight into slots
4–6, a doubleword at a time: 768 bytes a table, 48 KiB in all, the static `combSym`. The
accumulator, in slots 0–3, starts at `[17 G]B` (`combStart`), and step `i` adds digit `i`'s
entry of table `i`: 64 additions of affine cached points (`addAffineOps`, seven
multiplications each), and no doublings.

The digits are secret: their entries are selected in constant time. The scalar's nibbles are
first copied into the working space, one a byte (`combCopy`), so that no step needs the
scalar's address, nor a shift by a secret-free but variable amount, which PPC64LE has only
by register. Step `i` (in `r15`) reads byte `i` of the copy, at an address from `r6` and `r15`
alone; the masks of the eight magnitudes `k = 1 … 8` (all ones exactly for `|d| = k`) are in
`maskReg k`, and the sign's (all ones for a negative digit) at byte `SGN` of the working
space. Every doubleword of every candidate of table `i` (at `r16`, advanced by 768 bytes a
step) is loaded into `r0`, ANDed with its candidate's mask and ORed into `r12`; `|d| = 0`
selects the identity's `[1, 1, 0]` (`r17` is 1 exactly then). A negative digit's entry is
then negated by exchanging `Y - X` and `Y + X`, and `2dT` with `0 - 2dT`, under the sign's
mask. `r15`, `r16` and `r17` are nonvolatile, which the field code never writes; the
static's address is taken with `adrSym`, which changes `lr` (saved by `scalarBase`).
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE

open VG.PPC64LE

/-! ## The tables -/

/-- The static holding the comb's tables. -/
def combSym : String := "VG_ED25519_COMB"

/-- Coordinate `c` of a cached entry: `Y - X` (`c = 0`), `Y + X` (`c = 1`), `2dT` (`c = 2`). -/
def combCoord (p : Spec.Ed25519.Point) (c : Nat) : Spec.X25519.Fe :=
  if c = 0 then p.X else if c = 1 then p.Y else p.Z

/-- Doubleword `j < 4` (limbs `2 j` and `2 j + 1`) of coordinate `c` of entry `m + 1` of
table `i`. -/
def combDw (i m c j : Nat) : Nat := (combCoord (combCached64 i (m + 1)) c).val / 2 ^ (64 * j) % 2 ^ 64

/-- Doubleword `q` of the tables: table `i = q / 96` takes 96, entry `m + 1` of it 12
(`m = q % 96 / 12`), coordinate `c` 4 (`c = q % 12 / 4`). -/
def combWord (q : Nat) : BitVec 64 := BitVec.ofNat 64 (combDw (q / 96) (q % 96 / 12) (q % 12 / 4) (q % 4))

/-- The doublewords of the 64 tables, as the static `combSym` holds them. -/
def combWords : List (BitVec 64) := (List.range (64 * 96)).map combWord

/-- The static the comb reads. -/
def combConsts : List (String × List (BitVec 64)) := [(combSym, combWords)]

/-! ## The digits -/

/-- Byte of the working space holding the scalar's nibbles (`combCopy`). -/
def SCAL : Nat := 1152

/-- Byte of the working space holding the mask of the digit's sign. -/
def SGN : Nat := 56

/-- The registers of the masks of the magnitudes `1 … 8`. -/
def maskReg : Nat → Reg
  | 1 => .r3 | 2 => .r4 | 3 => .r5 | 4 => .r7 | 5 => .r8 | 6 => .r9 | 7 => .r10 | _ => .r11

/-- The mask of magnitude `k` into its register: all ones if `r12 = k`, else zero
(`r12 ⊕ k - 1` is negative exactly when `r12 = k`), from the zero in `r0`. -/
def combMask (k : Nat) : List Instr :=
  [.li (maskReg k) k, .logic .xor (maskReg k) .r12 (maskReg k), .subi (maskReg k) (maskReg k) 1,
    .lsr .d (maskReg k) (maskReg k) 63, .sub (maskReg k) .r0 (maskReg k)]

/-- Byte `k` of the scalar, at `r14`, as its two nibbles at bytes `SCAL + 2 k` (the low) and
`SCAL + 2 k + 1` (the high) of the working space; 15 in `r7`. -/
def combNibbles (k : Nat) : List Instr :=
  [.lbz .r8 .r14 k, .logic .and .r9 .r8 .r7, .stb .r9 .r6 (SCAL + 2 * k), .lsr .d .r9 .r8 4,
    .stb .r9 .r6 (SCAL + 2 * k + 1)]

/-- The scalar's 64 nibbles, a byte each, from byte `SCAL` of the working space, so that the
steps read them at addresses from `r6` alone. -/
def combCopy : List Instr := [.li .r7 15] ++ (List.range 32).flatMap combNibbles

/-- Digit `r15`: its nibble from the copy, then its sign's mask to byte `SGN`, its magnitude
into `r12`, and the masks of the magnitudes into `maskReg 1 … 8`; zero in `r0`, and in `r17` 1
if the magnitude is 0, else 0. -/
def combDigit : List Instr :=
  [.add .r12 .r6 .r15, .lbz .r12 .r12 SCAL,
    .li .r0 0, .subi .r12 .r12 8, .lsr .d .r11 .r12 63, .sub .r11 .r0 .r11,
    .store .d .r11 .r6 SGN, .logic .xor .r12 .r12 .r11, .sub .r12 .r12 .r11] ++
  (List.range 8).flatMap (fun k => combMask (k + 1)) ++
  [.subi .r17 .r12 1, .lsr .d .r17 .r17 63]

/-! ## The selection -/

/-- Candidate `m + 1`'s doubleword at `r16 + d`, masked and ORed into `r12`. -/
def selectCand (d m : Nat) : List Instr :=
  [.load .d .r0 .r16 d, .logic .and .r0 .r0 (maskReg (m + 1)), .logic .or .r12 .r12 .r0]

/-- Doubleword `j` of coordinate `c` of the digit's entry into slot `4 + c`: the identity's
(`1` for doubleword 0 of `Y - X` and `Y + X`) where `|d| = 0`, else candidate `|d|`'s. -/
def selectDw (c j : Nat) : List Instr :=
  (if c < 2 ∧ j = 0 then [.addi .r12 .r17 0] else [.li .r12 0]) ++
    (List.range 8).flatMap (fun m => selectCand (96 * m + 32 * c + 8 * j) m) ++
    [.store .d .r12 .r6 (64 + 32 * (4 + c) + 8 * j)]

/-- The digit's entry of table `r16` into slots 4–6, the identity's for `|d| = 0`. -/
def combSelect : List Instr := (List.range 12).flatMap fun q => selectDw (q / 4) (q % 4)

/-- The entry in slots 4–6 negated if the digit is negative: `Y - X` and `Y + X` exchanged,
and `2dT` with `0 - 2dT` (in slot 7, from the zero in slot 21), under the sign's mask. -/
def combNeg : Prog isa :=
  .seq (fieldCode [.sub 7 21 6])
    (.block ([.load .d .r11 .r6 SGN] ++ cswap (offset 4) (offset 5) ++ cswap (offset 6) (offset 7)))

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

/-- Step `r15 = i`: digit `i`'s entry of table `i` (at `r16`), negated for a negative digit,
added to the accumulator; `r7` nonzero while another step follows. -/
def combStep : Prog isa :=
  .seq (.block (combDigit ++ combSelect)) <|
  .seq combNeg <|
  .seq (fieldCode addAffineOps) (.block [.addi .r15 .r15 1, .addi .r16 .r16 768, .subi .r7 .r15 64])

/-- `(x, y)` of `[17 G]B`. -/
def combStartAff : Spec.X25519.Fe × Spec.X25519.Fe :=
  (4650268310714759443145295274883477433952106455267492499975084996511359585556,
    4189685876054382644851338298926788466640410231895644581786650308218358658796)

/-- `[17 G]B`, with `Z = 1`: where the accumulator starts. -/
def combStart : Spec.Ed25519.Point :=
  ⟨combStartAff.1, combStartAff.2, 1, combStartAff.1 * combStartAff.2⟩

/-- The accumulator at `[17 G]B`, zero in slot 21, the counter and the tables' address. -/
def combInit : Prog isa :=
  .seq (fieldCode ([.const 21 0] ++ constPointOps combStart)) (.block [.li .r15 0, .adrSym .r16 combSym])

/-- The scalar's nibbles, then the accumulator at `[17 G]B`, the counter and the tables. -/
def combPrepare : Prog isa := .seq (.block combCopy) combInit

/-- `[s]B` into slots 0–3, for the scalar at `r14`. -/
def combMultiply : Prog isa := .seq combPrepare (.loop combStep (.nonzero .d .r7))

end VG.Impl.Ed25519.PPC64LE
