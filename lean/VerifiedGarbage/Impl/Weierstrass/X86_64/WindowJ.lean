import VerifiedGarbage.Impl.Weierstrass.X86_64.Window
import VerifiedGarbage.Impl.Weierstrass.JacAdd

/-!
# Short Weierstrass curves on x86-64: windows in Jacobian coordinates

The window method of `Window.lean` (the same recoding, table selection and
negation), but keeping `R` in Jacobian coordinates from one window to the
next, and adding the entries by the mixed addition (`maddJ`, 11 products),
which saves each window the conversions into Jacobian coordinates and back
and the complete addition's 29 field additions and 3 of its products.

The table of `Window.lean` (`build`, projective) is brought into affine
coordinates by one inversion (`normTbl`, Montgomery's trick: the prefix
products of the entries' `Z`, the inversion `inv` of the last, then back
from entry `8`). For a curve whose points all have order `n` (prime), an
iteration's addition `[16 e]P + [d]P` for `|d| ≤ 8` has operands that are
neither equal nor opposite, unless one of them is `O`, as long as
`16 e + 8 < n`: which holds of every digit but the last. So each iteration
but the last (`stepJ`) adds the entry by the mixed addition (into `D`), then
keeps it, or `E` where `R` is `O`, or `R` where `E` is `O` (`selSum`, by
masks of their `Z` being zero). The last digit's iteration (`stepLast`) adds
by the complete formulas, `R` into projective coordinates first
(`toProjR`), so `R` ends in projective coordinates as in `window`.
-/

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

namespace WinCfg

variable (K : WinCfg)

/-- The prefix products of the table's `Z`, `c_m = Z_1 ⋯ Z_m`: `c_1` is
`Z_1`, `c_2 … c_7` in the addition's temporaries, `c_8` in `R.z`. -/
def prodSl : Nat → Nat
  | 2 => K.S.t0
  | 3 => K.S.t1
  | 4 => K.S.t2
  | 5 => K.S.t3
  | 6 => K.S.t4
  | 7 => K.S.t5
  | 8 => K.R.z
  | _ => (K.tblPt 1).z

/-- `c_2 … c_8`. -/
def prodOps : List FOp :=
  (List.range 7).map fun i => .mul (prodSl K (i + 2)) (prodSl K (i + 1)) (K.tblPt (i + 2)).z

/-- Entry `m ≥ 2` into affine coordinates, from `c_m^(p-2)` in `E.x`:
`D.x = c_m^(p-2) c_{m-1} = Z_m^(p-2)`, `E.x = c_m^(p-2) Z_m = c_{m-1}^(p-2)`,
and `X`, `Y` times `D.x`. -/
def backOps (m : Nat) : List FOp :=
  [.mul K.D.x K.E.x (prodSl K (m - 1)), .mul K.E.x K.E.x (K.tblPt m).z,
    .mul (K.tblPt m).x (K.tblPt m).x K.D.x, .mul (K.tblPt m).y (K.tblPt m).y K.D.x]

/-- Entries `8` down to `2`, then entry `1` (by `E.x = Z_1^(p-2)`). -/
def normOps : List FOp :=
  (List.range 7).flatMap (fun i => backOps K (8 - i)) ++
    [.mul (K.tblPt 1).x (K.tblPt 1).x K.E.x, .mul (K.tblPt 1).y (K.tblPt 1).y K.E.x]

/-- The table into affine coordinates, by one inversion (Montgomery's
trick): the prefix products, `inv` (`E.x = R.z^(p-2)`), the entries' `X` and
`Y` by their `Z^(p-2)`, and every `Z` one. -/
def normTbl (inv : Prog isa) : Prog isa :=
  .seq (fprogB K.M (prodOps K)) <| .seq inv <| .seq (fprogB K.M (normOps K)) <|
  .block ((List.range 8).flatMap fun i => setConst K.M.n (K.tblPt (i + 1)).z K.one)

/-- A pair of Jacobian doublings, `a` into `b` and back, with the public
count in the bits above the window index in `rbx`, as `jacPair`. -/
def jacPairOn (a b : Pt) : Prog isa :=
  .seq (fprogB K.M (double K a b)) <|
  .seq (fprogB K.M (double K b a)) <|
  .block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)]

/-- `R = 16 R` in Jacobian coordinates: two pairs of doublings between `R`
and `D`. -/
def quadJ : Prog isa := .seq (.block [.alu .add .rbx (.imm 8192)]) (.loop (jacPairOn K K.R K.D) .ae)

/-- The mask `rdx` of `[z] = 0` (all ones if it is), as `zeroMask`. -/
def zmask (z : Nat) : List Instr :=
  ([.mov .rdx (.mem (sc z))] : List Instr) ++ (((List.range (K.M.n - 1)).map fun j => .alu .or .rdx (.mem (sc (z + 8 * (j + 1))))) : List Instr) ++
  ([.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr)

/-- After the Jacobian addition into `D`: `D = R` where `E` is `O`, then
`R = E` where `R` is `O`, else `D` (the masks in `rcx`). -/
def selSum : List Instr :=
  zmask K K.E.z ++ [.mov .rcx (.reg .rdx)] ++ selPt K.M.n K.D K.D K.R ++
    zmask K K.R.z ++ [.mov .rcx (.reg .rdx)] ++ selPt K.M.n K.R K.D K.E

/-- `R = R + E` for an affine `E`, by the mixed addition, unless `R` and `E`
are equal but not `O`. -/
def sumJ : Prog isa :=
  .seq (fprogB K.M (maddJ K.S K.R K.E K.D)) (.block (selSum K))

/-- Iteration `j = rbx - 1 ≥ 1` (with `rbx` counting down from `J`):
`R = 16 R + [d_j]P` in Jacobian coordinates; then `ZF` of `rbx = 1`. -/
def stepJ : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (quadJ K) <|
  .seq (.block ((tc K).digit ++ select K)) <|
  .seq (.block (tc K).negY) <|
  .seq (sumJ K) <|
  .block [.alu .cmp .rbx (.imm 1)]

/-- `R` from Jacobian into projective coordinates `(XZ : Y : Z³)` (through
`D`), with `Y` Montgomery's one where `Z` (so `Z³`) is zero. -/
def toProjR : Prog isa :=
  .seq (fprogB K.M (fromJ K.S K.R (zeroPt K) K.D)) <|
  .block (copyPt K.M.n K.R K.D ++ zmask K K.R.z ++ (List.range K.M.n).flatMap (ySelWord K))

/-- The last iteration, `j = 0` (with `rbx = 1`): `R = 16 R` in Jacobian
coordinates, `R` into projective coordinates, and its sum with the entry
(affine, so projective too) by the complete formulas. -/
def stepLast : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (quadJ K) <|
  .seq (toProjR K) <|
  .seq (.block ((tc K).digit ++ select K)) <|
  .seq (.block (tc K).negY) <|
  .seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))

/-- `[k]P` into `R`, for the table of the bits of `k + offset J` at `K.bits`
(`J ≥ 2`), with `inv` leaving `R.z^(p-2)` in `E.x`. -/
def windowJ (inv : Prog isa) : Prog isa :=
  .seq (build K) <| .seq (normTbl K inv) <| .seq (.block (init K)) <| .seq (.loop (stepJ K) .ne) (stepLast K)

end WinCfg

end VG.Impl.Weierstrass.X86_64
