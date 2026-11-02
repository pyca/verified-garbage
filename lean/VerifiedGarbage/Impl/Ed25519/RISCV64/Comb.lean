module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.FieldMemory
public import VerifiedGarbage.Impl.Ed25519.CombTable16

/-!
# Ed25519: base-point multiplication with a comb, one table per digit, on RISC-V

ARMv7's comb (`Impl/Ed25519/Arm/Comb.lean`) on RISC-V's field code. The scalar's 64
nibbles `n_i` give `[s]B = Σ d_i [16^i]B + [17 G]B` for the digits `d_i = n_i - 8`, from
`-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`. Table `i` holds `[k]([16^i]B)` for `k = 1 … 8`
(`combCached64`), affine and cached (`[Y - X, Y + X, 2dT]`), each coordinate as the eight
32-bit limbs a field slot holds, so that a selected entry is stored straight into slots
4–6: 768 bytes a table, 48 KiB in all, the static `combSym`. The accumulator, in slots 0–3,
starts at `[17 G]B` (`combStart`), and step `i` adds digit `i`'s entry of table `i`: 64
additions of affine cached points (`addAffineOps`, seven multiplications each), and no
doublings.

The digits are secret: their entries are selected in constant time. The scalar is first
copied into the working space (`combCopy`), so that no step needs its address. Step `i`
(in `s1`) reads byte `i / 2` of the copy and shifts it right by `4 (i mod 2)`, both public; the masks of the eight magnitudes `k = 1 … 8` (all ones exactly
for `|d| = k`) are in `maskReg k`, and the sign's (all ones for a negative digit) at byte
`SGN` of the working space. Every doubleword of every candidate of table `i` (at `s2`,
advanced by 768 bytes a step) is loaded, ANDed with its candidate's mask and ORed into
`a4`; `|d| = 0` selects the identity's `[1, 1, 0]`. A negative digit's entry is then
negated by exchanging `Y - X` and `Y + X`, and `2dT` with `0 - 2dT`, under the sign's mask.
The addresses depend on the working space's, the static's and `s1` alone; `s1` and `s2`
are callee-saved, which the field code never writes.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.X25519.RISCV64 (cswap)

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

/-- Byte of the working space holding the scalar's copy (`combCopy`). -/
def SCAL : Nat := 1152

/-- Byte of the working space holding the mask of the digit's sign. -/
def SGN : Nat := 56

/-- The registers of the masks of the magnitudes `1 … 8`. -/
def maskReg : Nat → Reg
  | 1 => .t1 | 2 => .t2 | 3 => .t3 | 4 => .t4 | 5 => .t5 | 6 => .t6 | 7 => .a6 | _ => .a7

/-- The mask of magnitude `k` into its register: all ones if `a4 = k`, else zero
(`a4 ⊕ k - 1` is negative exactly when `a4 = k`), from the zero in `a0`. -/
def combMask (k : Nat) : List Instr :=
  [.logicImm .xor (maskReg k) .a4 k, .addi (maskReg k) (maskReg k) (-1),
    .shift .srl .d (maskReg k) (maskReg k) 63, .sub (maskReg k) .a0 (maskReg k)]

/-- The scalar, at `s0`, copied to byte `SCAL` of the working space, so that the steps read
it at addresses from `a3` alone. -/
def combCopy : List Instr :=
  (List.range 32).flatMap fun k => [.load .b .a4 .s0 k, .store .b .a4 .a3 (SCAL + k)]

/-- Digit `s1`: the nibble of byte `s1 / 2` of the scalar's copy (its high nibble for odd `s1`,
by a shift of the public `4 (s1 mod 2)`), then its sign's mask to byte `SGN`, its magnitude
into `a4`, and the masks of the magnitudes into `maskReg 1 … 8`; zero in `a0`, and in `t0` 1
if the magnitude is 0, else 0. -/
def combDigit : List Instr :=
  [.shift .srl .d .a1 .s1 1, .add .a1 .a3 .a1, .load .b .a2 .a1 SCAL,
    .logicImm .and .t0 .s1 1, .shift .sll .d .t0 .t0 2, .shiftReg .srl .d .a4 .a2 .t0,
    .logicImm .and .a4 .a4 15,
    .li .a0 0, .addi .a4 .a4 (-8), .shift .srl .d .a5 .a4 63, .sub .a5 .a0 .a5,
    .store .d .a5 .a3 SGN, .logic .xor .a4 .a4 .a5, .sub .a4 .a4 .a5] ++
  (List.range 8).flatMap (fun k => combMask (k + 1)) ++
  [.sltu .t0 .a0 .a4, .logicImm .xor .t0 .t0 1]

/-! ## The selection -/

/-- Candidate `m + 1`'s doubleword at `s2 + d`, masked and ORed into `a4`. -/
def selectCand (d m : Nat) : List Instr :=
  [.load .d .a5 .s2 d, .logic .and .a5 .a5 (maskReg (m + 1)), .logic .or .a4 .a4 .a5]

/-- Doubleword `j` of coordinate `c` of the digit's entry into slot `4 + c`: the identity's
(`1` for doubleword 0 of `Y - X` and `Y + X`) where `|d| = 0`, else candidate `|d|`'s. -/
def selectDw (c j : Nat) : List Instr :=
  (if c < 2 ∧ j = 0 then [.addi .a4 .t0 0] else [.li .a4 0]) ++
    (List.range 8).flatMap (fun m => selectCand (96 * m + 32 * c + 8 * j) m) ++
    [.store .d .a4 .a3 (64 + 32 * (4 + c) + 8 * j)]

/-- The digit's entry of table `s2` into slots 4–6, the identity's for `|d| = 0`. -/
def combSelect : List Instr := (List.range 12).flatMap fun q => selectDw (q / 4) (q % 4)

/-- The entry in slots 4–6 negated if the digit is negative: `Y - X` and `Y + X` exchanged,
and `2dT` with `0 - 2dT` (in slot 7, from the zero in slot 21), under the sign's mask. -/
def combNeg : Prog isa :=
  .seq (fieldCode [.sub 7 21 6])
    (.block ([.load .d .t0 .a3 SGN] ++ cswap (offset 4) (offset 5) ++ cswap (offset 6) (offset 7)))

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

/-- Step `s1 = i`: digit `i`'s entry of table `i` (at `s2`), negated for a negative digit,
added to the accumulator; `a4` nonzero while another step follows. -/
def combStep : Prog isa :=
  .seq (.block (combDigit ++ combSelect)) <|
  .seq combNeg <|
  .seq (fieldCode addAffineOps) (.block [.addi .s1 .s1 1, .addi .s2 .s2 768, .addi .a4 .s1 (-64)])

/-- `(x, y)` of `[17 G]B`. -/
def combStartAff : Spec.X25519.Fe × Spec.X25519.Fe :=
  (4650268310714759443145295274883477433952106455267492499975084996511359585556,
    4189685876054382644851338298926788466640410231895644581786650308218358658796)

/-- `[17 G]B`, with `Z = 1`: where the accumulator starts. -/
def combStart : Spec.Ed25519.Point :=
  ⟨combStartAff.1, combStartAff.2, 1, combStartAff.1 * combStartAff.2⟩

/-- The accumulator at `[17 G]B`, zero in slot 21, the counter and the tables' address. -/
def combInit : Prog isa :=
  .seq (fieldCode ([.const 21 0] ++ constPointOps combStart)) (.block [.li .s1 0, .lla .s2 combSym])

/-- The scalar's copy, then the accumulator at `[17 G]B`, the counter and the tables. -/
def combPrepare : Prog isa := .seq (.block combCopy) combInit

/-- `[s]B` into slots 0–3, for the scalar at `s0`. -/
def combMultiply : Prog isa := .seq combPrepare (.loop combStep (.nonzero .a4))

end VG.Impl.Ed25519.RISCV64
