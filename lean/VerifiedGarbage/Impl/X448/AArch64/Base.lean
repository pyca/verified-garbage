import VerifiedGarbage.Impl.X448.AArch64.Field56
import VerifiedGarbage.Impl.X448.BaseTable

/-!
# X448 of the base point on AArch64: a fixed-base multiplication on edwards448

`vg_x448_base(out = x0, scalar = x1, scratch = x2)` computes `X448(k, 5)` as
the u-coordinate `y² / x²` of `[k] B` on edwards448 (Ed448's curve), `B` its
base point (RFC 7748 §4.2's 4-isogeny; `Proof/X448/Edwards/Ladder.lean`).

`[k] B` is a comb, as Ed25519's (`Impl/Ed25519/AArch64/Comb.lean`): the
scalar's 112 nibbles `n_i` give `[k] B = Σ d_i [16^i] B + [17 G] B` for the
digits `d_i = n_i - 8`, from `-8` to `7`, and `G = 8 Σ_{j < 56} 256^j`. Table
`j` holds `[m · 256^j] B` for `m ≤ 8` (`baseTable`, affine); the 57 tables are
the static `combSym` (`combWords`, 1024 bytes a table). Step `j` selects from
table `j` the entries of `d_{2j+1}` and `d_{2j}`, sharing each candidate's
load between the two, negates them for negative digits
(`(x, y) ↦ (-x, y)`), and adds them to two projective accumulators, which start
at `[G] B`: `A` (slots 0–2) for the odd digits and `B` (slots 3–5) for the even
ones. At the end, `[k] B = 16 A + B`: four doublings and one addition, with
the complete addition law (RFC 8032 §5.2.4).

The field operations are those of the ladder (`Impl/Curve448/AArch64/Fast.lean`,
eight 56-bit limbs per 128-byte slot): products take operands whose limbs are
below `Ib` and give limbs below `Mb`; sums and differences take reduced
operands. So an addition computes `x₁y₂ + y₁x₂` with two products (not as
`(x₁ + y₁)(x₂ + y₂) - x₁x₂ - y₁y₂`), and `b ∓ d·c·e` with `small`
(`a + 39081 e`, `d = -39081`) of `c·e` and of its negation: one square and ten
products (`addOps`). Adding an affine entry (`addAffine`), eight of them are
four pairs of AdvSIMD multiplications (`Impl/Curve448/AArch64/Neon.lean`), each
interleaved with independent scalar operations, as the ladder's steps are. The
function saves `v8`–`v15`.

Then `X448(k, 5) = Y² / X²` (`Y` and `X` of `[k] B`): the squares go to the
ladder's `X2` and `Z2`, inverted and multiplied as the ladder's result is
(`Fast.invert`, `finish`).

The output pointer stays in `x20`, which no field operation writes. The
digits are secret: their entries are selected in constant time. Their
masks (all ones exactly for `|d| = m`, `m = 1 … 8`) and the bit of `|d| = 0`
stay in registers (`oddRegs`, `x5`; `evenRegs`, `x0`) while each candidate
word is loaded from the table and ORed in under each mask: every entry of
the table is read, at addresses from the static's and the loop's counter
`x19`, the table index, which is public; the branches are on it alone.
-/

namespace VG.Impl.X448.AArch64.Base

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot BITS X2 Z2 T7)
open VG.Impl.X448.AArch64.Fast (codeOf save restore)

/-! ## Layout -/

/-- The accumulators: `A` (odd digits) in slots 0–2, `B` (even) in slots 3–5. -/
def AX : Nat := slot 0
def AY : Nat := slot 1
def AZ : Nat := slot 2
def BX : Nat := slot 3
def BY : Nat := slot 4
def BZ : Nat := slot 5
/-- The selected entries, affine: the odd digit's in slots 6–7, the even's in 8–9. -/
def OX : Nat := slot 6
def OY : Nat := slot 7
def EX : Nat := slot 8
def EY : Nat := slot 9
/-- The additions' temporaries (slots 10–18), and zero (slot 19): with slots 20–21, every
slot is one of the ladder's 22 (`Proof/X448/AArch64/Weak/Env.lean`). -/
def t (i : Nat) : Nat := slot (10 + i)
def ZERO : Nat := slot 19

/-! ## Point arithmetic -/

/-- `(X₁ : Y₁ : Z₁) + (X₂ : Y₂ : Z₂)` into `(X₁, Y₁, Z₁)`, by RFC 8032 §5.2.4's
complete law (`d = -39081`): `a = Z₁Z₂`, `b = a²`, `c = X₁X₂`, `e = Y₁Y₂`,
`f = b - d·c·e`, `g = b + d·c·e`, `k = X₁Y₂ + Y₁X₂`, and `(a·f·k, a·g·(e - c), f·g)`.
No operation's output is one of its operands, but `small`'s first. -/
def addOps (x1 y1 z1 x2 y2 z2 : Nat) : List Fast.Op :=
  [.mul (t 0) z1 z2, .mul (t 1) (t 0) (t 0), .mul (t 2) x1 x2, .mul (t 3) y1 y2,
   .mul (t 4) (t 2) (t 3), .small (t 5) (t 1) (t 4), .sub (t 6) ZERO (t 4),
   .small (t 1) (t 1) (t 6), .mul (t 4) x1 y2, .mul (t 6) y1 x2,
   .addSub (t 7) (t 8) (t 4) (t 6), .addSub (t 4) (t 6) (t 3) (t 2),
   .mul (t 2) (t 0) (t 5), .mul x1 (t 2) (t 7), .mul (t 3) (t 0) (t 1), .mul y1 (t 3) (t 6),
   .mul z1 (t 5) (t 1)]

/-- `(X : Y : Z) + (x, y)` into `(X, Y, Z)`: `addOps` with `Z₂ = 1`, so `a = Z`, its
pairs of independent products in AdvSIMD (`Neon.mul2`), each interleaved with scalar
operations independent of it, as the ladder's steps are; `Z` is `f·g` through `t 8`. -/
def addAffine (x1 y1 z1 x2 y2 : Nat) : List Instr :=
  Fast.weave (codeOf [.mul (t 0) z1 z1])
    (Curve448.AArch64.Neon.mul2 (t 1) x1 x2 (t 2) y1 y2) ++
  Fast.weave (codeOf [.mul (t 3) (t 1) (t 2), .small (t 4) (t 0) (t 3), .sub (t 5) ZERO (t 3),
      .small (t 0) (t 0) (t 5)])
    (Curve448.AArch64.Neon.mul2 (t 6) x1 y2 (t 7) y1 x2) ++
  codeOf [.addSub (t 3) (t 5) (t 6) (t 7), .addSub (t 6) (t 7) (t 2) (t 1)] ++
  Fast.weave (codeOf [.mul (t 8) (t 4) (t 0)])
    (Curve448.AArch64.Neon.mul2 (t 1) z1 (t 4) (t 2) z1 (t 0)) ++
  Fast.weave (codeOf [.copy z1 (t 8)])
    (Curve448.AArch64.Neon.mul2 x1 (t 1) (t 3) y1 (t 2) (t 7))

/-! ## Constants -/

/-- `d := v`, from immediates. -/
def const64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x d (v.extractLsb' 0 16) 0, .movk .x d (v.extractLsb' 16 16) 1,
   .movk .x d (v.extractLsb' 32 16) 2, .movk .x d (v.extractLsb' 48 16) 3]

/-- Limb `w` of a field element, in radix `2⁵⁶`. -/
def limb (v : Spec.X448.Fe) (w : Nat) : BitVec 64 := BitVec.ofNat 64 ((v.val >>> (56 * w)) % 2 ^ 56)

/-- The slot at `o` := `v`. -/
def constSlot (o : Nat) (v : Spec.X448.Fe) : List Instr :=
  (List.range 8).flatMap fun w => const64 .x4 (limb v w) ++ [st .x4 (o + 8 * w)]

/-! ## Digits and selection -/

/-- The registers holding the masks of the odd digit's magnitudes `1 … 8` (not `x12`,
which holds `2²⁸ - 1` for the vector products). -/
def oddRegs : List Reg := [.x10, .x11, .x13, .x14, .x15, .x16, .x17, .x4]

/-- The registers holding the masks of the even digit's magnitudes `1 … 8`. -/
def evenRegs : List Reg := [.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

def oddReg (m : Nat) : Reg := oddRegs.getD (m - 1) .x10
def evenReg (m : Nat) : Reg := evenRegs.getD (m - 1) .x21

/-- `x2` = the nibble `b₀ + 2b₁ + 4b₂ + 8b₃` of the bits at `x8 + o`. -/
def nibble (o : Nat) : List Instr :=
  [.ldrb .x2 .x8 (o + 3), .add .x .x2 .x2 .x2, .ldrb .x9 .x8 (o + 2), .add .x .x2 .x2 .x9,
    .add .x .x2 .x2 .x2, .ldrb .x9 .x8 (o + 1), .add .x .x2 .x2 .x9,
    .add .x .x2 .x2 .x2, .ldrb .x9 .x8 o, .add .x .x2 .x2 .x9]

/-- `x2` := `|n - 8|`, for the nibble `n` in `x2`. -/
def magnitude : List Instr :=
  [.subImm .x .x9 .x2 8, .lsr .x .x1 .x9 63, .movz .w .x2 0 0, .sub .x .x1 .x2 .x1,
    .logic .eor .x .x2 .x9 .x1, .sub .x .x2 .x2 .x1]

/-- `z` = `[|d| < 1]` and `rs[m - 1]` = all ones exactly if `|d| = m`, for `|d|` in `x2`. -/
def masks (rs : List Reg) (z : Reg) : List Instr :=
  [.subImm .x z .x2 1, .lsr .x z z 63] ++
    (List.range 8).flatMap (fun m =>
      [.subImm .x (rs.getD m .x10) .x2 (m + 1), .lsr .x (rs.getD m .x10) (rs.getD m .x10) 63]) ++
    (List.range 8).map fun m =>
      if m < 7 then .sub .x (rs.getD m .x10) (rs.getD m .x10) (rs.getD (m + 1) .x10)
      else .subImm .x (rs.getD m .x10) (rs.getD m .x10) 1

/-- Both digits of step `x19 = j`: `d_{2j+1}` (bits at `BITS + 8j + 4`) to `oddRegs` and
`x5`, `d_{2j}` (bits at `BITS + 8j`) to `evenRegs` and `x0`. -/
def digits : List Instr :=
  [.lsl .x .x8 .x19 3, .add .x .x8 .x3 .x8] ++
    nibble (BITS + 4) ++ magnitude ++ masks oddRegs .x5 ++
    nibble BITS ++ magnitude ++ masks evenRegs .x0

/-! ## The tables -/

/-- The static holding the comb's tables. -/
def combSym : String := "VG_X448_COMB"

/-- Word `i` of the tables: table `j = i / 128` takes 1024 bytes, the `x` (`c = 0`) then the
`y` (`c = 1`) of its entries `m + 1 = 1 … 8`, eight limbs each. -/
def combWord (i : Nat) : BitVec 64 :=
  let e := Impl.X448.baseTable (i / 128) (i % 64 / 8 + 1)
  limb (if i % 128 < 64 then e.1 else e.2) (i % 8)

/-- The words of the 57 tables, as the static `combSym` holds them. -/
def combWords : List (BitVec 64) := (List.range (57 * 128)).map combWord

/-- The static the comb reads. -/
def combConsts : List (String × List (BitVec 64)) := [(combSym, combWords)]

/-- `x9` = the address of table `x19`: the static's, plus 1024 bytes a table. -/
def tblAddr : List Instr := [.adrSym .x9 combSym, .lsl .x .x8 .x19 10, .add .x .x9 .x9 .x8]

/-- Word `w` of the coordinate (`y` if `one`, else `x`) of entry `|d|` of the table at `x9`
(entry 0, the identity `(0, 1)`, from the bits of `|d| = 0`) for both digits, to `o + 8w`
(odd) and `e + 8w` (even). -/
def selectWord (one : Bool) (o e w : Nat) : List Instr :=
  (if one && w == 0 then [.addImm .x .x1 .x5 0, .addImm .x .x2 .x0 0]
   else [.movz .w .x1 0 0, .movz .w .x2 0 0]) ++
  (List.range 8).flatMap (fun m =>
    [.ldr .x .x6 .x9 ((if one then 512 else 0) + 64 * m + 8 * w),
      .logic .and .x .x7 .x6 (oddReg (m + 1)), .logic .orr .x .x1 .x1 .x7,
      .logic .and .x .x7 .x6 (evenReg (m + 1)), .logic .orr .x .x2 .x2 .x7]) ++
  [st .x1 (o + 8 * w), st .x2 (e + 8 * w)]

/-- Both digits' entries of table `x19`. -/
def select : List Instr :=
  tblAddr ++ (List.range 8).flatMap (selectWord false OX EX) ++
    (List.range 8).flatMap (selectWord true OY EY)

/-- The entry's `x` at `ox` negated if its digit is negative, that is if the top bit of its
nibble (at `x3 + 8 x19 + o + 3`) is clear, its mask `bit - 1` all ones; `w` is a
temporary. -/
def negate (ox o w : Nat) : List Instr :=
  codeOf [.sub w ZERO ox] ++
    [.lsl .x .x6 .x19 3, .add .x .x6 .x3 .x6, .ldrb .x6 .x6 (o + 3), .subImm .x .x6 .x6 1] ++
    Curve448.AArch64.cswap ox w

/-! ## The function -/

/-- Save the registers, keep the output pointer in `x20`, set `x12` to `2²⁸ - 1` and every slot to
zero. -/
def entry : List Instr :=
  [.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
    st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] ++ save ++ Fast.vsave ++ [.movz .x .x4 0 0] ++
    (List.range 352).map (fun i => st .x4 (slot 0 + 8 * i))

/-- Both accumulators at the affine point `g`, and the counter at 0. -/
def accs (g : Spec.X448.Fe × Spec.X448.Fe) : List Instr :=
  constSlot AX g.1 ++ constSlot AY g.2 ++ constSlot AZ 1 ++
    constSlot BX g.1 ++ constSlot BY g.2 ++ constSlot BZ 1 ++ [.movz .x .x19 0 0]

/-- `entry`, the clamped scalar's bits, and both accumulators at `[G] B`. -/
def setup : Prog isa :=
  .seq (.block entry) <| .seq AArch64.bits <| .block (accs baseG)

/-- `Y²` to `X2` and `X²` to `Z2`, as the ladder leaves `x₂` and `z₂`, then `Y² / X²`,
frozen and packed to the output, and the registers restored. -/
def finish : Prog isa :=
  .seq (.block (codeOf [.mul X2 AY AY, .mul Z2 AX AX])) <|
  .seq Fast.invert <|
  .block (.addImm .x .x1 .x20 0 :: Fast.fmul X2 X2 T7 ++ Curve448.AArch64.toLegacy X2 ++
    AArch64.freeze ++ (List.range 8).flatMap AArch64.packPair ++ [ld .x19 0, ld .x20 8] ++
    restore ++ Fast.vrestore)

end VG.Impl.X448.AArch64.Base
