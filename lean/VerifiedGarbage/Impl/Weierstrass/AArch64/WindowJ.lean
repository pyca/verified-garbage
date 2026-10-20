module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Window
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ

/-!
# Short Weierstrass curves on AArch64: windows in Jacobian coordinates

The window method of `Window.lean` (the same recoding, table, selection and
negation), but keeping `R` in Jacobian coordinates from one window to the
next, and adding the entries by the mixed addition (`maddJ`, 8 products and
3 squares), which saves each window the conversions into Jacobian
coordinates and back and the complete addition: as `windowJ` on x86-64
(`Impl/Weierstrass/X86_64/WindowJ.lean`).

The table of `Window.lean` (`build`, projective) is brought into affine
coordinates by one inversion (`normTbl`, Montgomery's trick: the prefix
products of the entries' `Z`, the inversion `inv` of the last, then back
from entry `8`). For a curve whose points all have order `n` (prime), an
iteration's addition `[16 e]P + [d]P` for `|d| ≤ 8` has operands that are
neither equal nor opposite, unless one of them is `O`, as long as
`16 e + 8 < n`: which holds of every digit but the last
(`Proof/Weierstrass/WindowJ.lean`). So each iteration but the last
(`stepJ`) adds the entry by the mixed addition (into `D`), then keeps it,
or `E` where `R` is `O`, or `R` where `E` is `O` (`selSum`, by masks of their
`Z` being zero). The last digit's iteration (`stepLast`) adds by the
complete formulas, `R` into projective coordinates first (`toProjR`), so `R`
ends in projective coordinates as in `window`.

The digits stay secret as in `window`: every entry's every word is loaded
and masked, and the sums are chosen by masks. The counter `x19` (its low
half the window, its high half the doublings) is public, as are every
address and branch.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

namespace WinCfg

variable (K : WinCfg)

/-- The prefix products of the table's `Z`, `c_m = Z_1 ⋯ Z_m`: `c_1` a copy
of `Z_1` in `D.z`, `c_2 … c_7` in the addition's temporaries, `c_8` in
`R.z`. -/
def prodSl : Nat → Nat
  | 2 => K.S.t0
  | 3 => K.S.t1
  | 4 => K.S.t2
  | 5 => K.S.t3
  | 6 => K.S.t4
  | 7 => K.S.t5
  | 8 => K.R.z
  | _ => K.D.z

/-- Pieces `0 … N - 1` of code, in order. -/
def seqRange (f : Nat → Prog isa) : Nat → Prog isa
  | 0 => .block []
  | i + 1 => .seq (seqRange f i) (f i)

/-- `o = a [b]` for `b` a slot of the table, copied into `D.y` first. -/
def mulTb (o a b : Nat) : Prog isa :=
  .seq (.block (copy K.M.n K.D.y b)) (fprogB K.M [.mul o a K.D.y])

/-- `[x] = [x] d` for `x` a slot of the table, through `D.y`. -/
def mulTx (x d : Nat) : Prog isa :=
  .seq (.block (copy K.M.n K.D.y x)) <| .seq (fprogB K.M [.mul K.D.y K.D.y d]) (.block (copy K.M.n x K.D.y))

/-- `c_{i+2} = c_{i+1} Z_{i+2}`. -/
def prodStep (i : Nat) : Prog isa := mulTb K (prodSl K (i + 2)) (prodSl K (i + 1)) (K.tblPt (i + 2)).z

/-- Entry `m ≥ 2` into affine coordinates, from `c_m^(p-2)` in `E.x`:
`D.x = c_m^(p-2) c_{m-1} = Z_m^(p-2)`, `E.x = c_m^(p-2) Z_m = c_{m-1}^(p-2)`,
and `X`, `Y` times `D.x`. -/
def backStep (m : Nat) : Prog isa :=
  .seq (fprogB K.M [.mul K.D.x K.E.x (prodSl K (m - 1))]) <|
  .seq (mulTb K K.E.x K.E.x (K.tblPt m).z) <|
  .seq (mulTx K (K.tblPt m).x K.D.x) (mulTx K (K.tblPt m).y K.D.x)

/-- Entry `1`, by `E.x = Z_1^(p-2)`. -/
def backOne : Prog isa := .seq (mulTx K (K.tblPt 1).x K.E.x) (mulTx K (K.tblPt 1).y K.E.x)

/-- The table into affine coordinates, by one inversion (Montgomery's
trick): `Z_1` copied into `D.z`, the prefix products, `inv` (`E.x =
R.z^(p-2)`), the entries' `X` and `Y` by their `Z^(p-2)` from entry `8`, and
every `Z` one. -/
def normTbl (inv : Prog isa) : Prog isa :=
  .seq (.block (copy K.M.n K.D.z (K.tblPt 1).z)) <| .seq (seqRange (prodStep K) 7) <| .seq inv <|
  .seq (seqRange (fun i => backStep K (8 - i)) 7) <| .seq (backOne K) <|
  .block ((List.range 8).flatMap fun i => setConst K.M.n (K.tblPt (i + 1)).z K.one)

/-- `R = 2R` into `D`: the doubling's field program by `fprogB`, or the
block `dd` gives (`Option`'s first, for `R` into `D`). -/
def dblRD (dd : Option (Prog isa × Prog isa)) : Prog isa :=
  match dd with
  | some d => d.1
  | none => fprogB K.M (double K K.R K.D)

/-- `D = 2D` into `R`, as `dblRD`. -/
def dblDR (dd : Option (Prog isa × Prog isa)) : Prog isa :=
  match dd with
  | some d => d.2
  | none => fprogB K.M (double K K.D K.R)

/-- A pair of Jacobian doublings, `R` into `D` and back, then the count in
the high half of `x19` less one, into `x2`, as `dbl2`. -/
def jacPair (dd : Option (Prog isa × Prog isa)) : Prog isa :=
  .seq (dblRD K dd) <| .seq (dblDR K dd) <|
  .block [.movz .x .x2 1 2, .sub .x .x19 .x19 .x2, .lsr .x .x2 .x19 32]

/-- `R = 16 R` in Jacobian coordinates: two pairs of doublings between `R`
and `D`. -/
def quadJ (dd : Option (Prog isa × Prog isa) := none) : Prog isa :=
  .seq (.block [.movz .x .x2 2 2, .add .x .x19 .x19 .x2]) (.loop (jacPair K dd) (.nonzero .x .x2))

/-- After the Jacobian addition into `D`: `D = R` where `E` is `O`, then
`R = E` where `R` is `O`, else `D` (the masks of `Z ≠ 0`, `nzMask`, in
`x3`). -/
def selSum : List Instr :=
  nzMask K.M.n K.E.z ++ selPt K.M.n K.D K.R K.D ++ nzMask K.M.n K.R.z ++ selPt K.M.n K.R K.E K.D

/-- `D = R + E` by the mixed addition: its field program by `fprogB`, or the
block `ma` gives. -/
def maddRD (ma : Option (Prog isa)) : Prog isa :=
  match ma with
  | some m => m
  | none => fprogB K.M (maddJ K.S K.R K.E K.D)

/-- `R = R + E` for an affine `E`, by the mixed addition (`maddRD`), unless
`R` and `E` are equal but not `O`. -/
def sumJ (ma : Option (Prog isa) := none) : Prog isa :=
  .seq (maddRD K ma) (.block (selSum K))

/-- The selection of digit `x19`'s entry into `E`: `sl` if given, else the
digit's masks and `select`. -/
def selOf (sl : Option (List Instr)) : List Instr :=
  match sl with
  | some c => c
  | none => digit K.bits ++ select K

/-- The entry of digit `x19` into `E` (by `selOf`), its `y` negated for a
negative digit. -/
def entry (sl : Option (List Instr) := none) : List Instr :=
  selOf K sl ++ negY K.M K.neg K.zero K.E.y K.bits

/-- Iteration `j = x19 - 1 ≥ 1`: `R = 16 R + [d_j]P` in Jacobian coordinates;
then `x4 = x19 - 1`, zero after the iteration of digit 1. -/
def stepJ (dd : Option (Prog isa × Prog isa) := none) (ma : Option (Prog isa) := none)
    (sl : Option (List Instr) := none) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (quadJ K dd) <| .seq (.block (entry K sl)) <|
  .seq (sumJ K ma) (.block [.subImm .x .x4 .x19 1])

/-- `R` from Jacobian into projective coordinates `(XZ : Y : Z³)` (through
`D`), with `Y` Montgomery's one where `Z` (so `Z³`) is zero. -/
def toProjR : Prog isa :=
  .seq (fprogB K.M (fromJ K.S K.R (zeroPt K) K.D)) <|
  .block (copyPt K.M.n K.R K.D ++ zeroMask K.M.n K.R.z ++ (List.range K.M.n).flatMap (ySelWord K))

/-- The last iteration, `j = 0` (with `x19 = 1`): `R = 16 R` in Jacobian
coordinates, `R` into projective coordinates, and its sum with the entry
(affine, so projective too) by the complete formulas. -/
def stepLast (pa : Option (String × Nat) := none) (dd : Option (Prog isa × Prog isa) := none)
    (sl : Option (List Instr) := none) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (quadJ K dd) <| .seq (toProjR K) <| .seq (.block (entry K sl)) <|
  .seq (addP K.M K.S K.R K.E K.D pa) (.block (copyPt K.M.n K.R K.D))

/-- `[k]P` into `R`, in projective coordinates, for the table of the bits of
`k + offset J` at `K.bits` (`J ≥ 2`), with `inv` leaving `R.z^(p-2)` in
`E.x`. The doublings are `dd`'s blocks if given, the mixed additions `ma`'s,
the entries' selections `sl`'s. -/
def windowJ (inv : Prog isa) (pa : Option (String × Nat) := none) (dd : Option (Prog isa × Prog isa) := none)
    (ma : Option (Prog isa) := none) (sl : Option (List Instr) := none) : Prog isa :=
  .seq (build K pa) <| .seq (normTbl K inv) <| .seq (.block (init K)) <|
  .seq (.loop (stepJ K dd ma sl) (.nonzero .x .x4)) (stepLast K pa dd sl)

end WinCfg

end VG.Impl.Weierstrass.AArch64
