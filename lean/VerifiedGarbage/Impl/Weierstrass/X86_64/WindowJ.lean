import VerifiedGarbage.Impl.Weierstrass.X86_64.Window
import VerifiedGarbage.Impl.Weierstrass.JacAdd

/-!
# Short Weierstrass curves on x86-64: windows in Jacobian coordinates

The window method of `Window.lean` (the same recoding, table selection and
negation), but keeping `R` in Jacobian coordinates from one window to the
next, and adding the entries in Jacobian coordinates too, which saves each
window the conversions into Jacobian coordinates and back and the complete
addition's 29 field additions, for a Jacobian addition's 7 (`jacHead`,
`jacTail`, 16 products, as many as the complete addition and its `toJ` and
`fromJ` save).

The table's entries are stored in Jacobian coordinates (`buildJ`: each entry
of the complete additions converted by `toJ` before it is stored, through
`R`). For a curve whose points all have order `n` (prime), an iteration's
addition `[16 e]P + [d]P` for `|d| ≤ 8` has operands that are neither equal
nor opposite, unless one of them is `O`, as long as `16 e + 8 < n`: which
holds of every digit but the last. So each iteration but the last (`stepJ`)
adds the entry by the Jacobian addition (into `D`), then keeps it, or `E`
where `R` is `O`, or `R` where `E` is `O` (`selSum`, by masks of their `Z`
being zero). The last digit's iteration (`stepLast`) adds by the complete
formulas, `R` and `E` into projective coordinates first (`toProjR`,
`toProjE`), so `R` ends in projective coordinates as in `window`.
-/

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

namespace WinCfg

variable (K : WinCfg)

/-- `src` into entry `8 - rbx` of the table, for `rbx ≤ j`: as `storeEntry`,
from any point. -/
def storeEntryOf (src : Pt) : Nat → Prog isa
  | 0 => .block (copyPt K.M.n (K.tblPt 8) src)
  | j + 1 => .seq (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 (j + 1)))])
      (.ite .e (.block (copyPt K.M.n (K.tblPt (7 - j)) src)) (storeEntryOf src j))

/-- An entry of the table, with `E = [m]P` and `rbx = 8 - m`: `D = E + P`
(`[m + 1]P`), `E = D`, and `D` in Jacobian coordinates (into `R`) into
entry `m + 1`. -/
def buildStepJ : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq (fprogB K.M (rcb3 K.S K.E K.P K.D)) <|
  .seq (.block (copyPt K.M.n K.E K.D)) <| .seq (fprogB K.M (toJ K.S K.D (zeroPt K) K.R)) <|
  .seq (storeEntryOf K K.R 6) (.block [.alu .test .rbx (.reg .rbx)])

/-- The table in Jacobian coordinates: `E = P`, `[1]P` (`P` in Jacobian
coordinates, through `R`), then a loop of seven additions (`buildStepJ`). -/
def buildJ : Prog isa :=
  .seq (.block (copyPt K.M.n K.E K.P)) <| .seq (fprogB K.M (toJ K.S K.E (zeroPt K) K.R)) <|
  .seq (.block (copyPt K.M.n (K.tblPt 1) K.R ++ [.mov32 .rbx (.imm 7)])) (.loop (buildStepJ K) .ne)

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
  [.mov .rdx (.mem (sc z))] ++ ((List.range (K.M.n - 1)).map fun j => .alu .or .rdx (.mem (sc (z + 8 * (j + 1))))) ++
  [.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)]

/-- After the Jacobian addition into `D`: `D = R` where `E` is `O`, then
`R = E` where `R` is `O`, else `D` (the masks in `rcx`). -/
def selSum : List Instr :=
  zmask K K.E.z ++ [.mov .rcx (.reg .rdx)] ++ selPt K.M.n K.D K.D K.R ++
    zmask K K.R.z ++ [.mov .rcx (.reg .rdx)] ++ selPt K.M.n K.R K.D K.E

/-- `R = R + E` in Jacobian coordinates, unless `R` and `E` are equal or
opposite but not `O`. -/
def sumJ : Prog isa :=
  .seq (fprogB K.M (jacHead K.S K.R K.E ++ jacTail K.S K.R K.E K.D)) (.block (selSum K))

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

/-- `E` from Jacobian into projective coordinates (through `D`). -/
def toProjE : Prog isa :=
  .seq (fprogB K.M (fromJ K.S K.E (zeroPt K) K.D)) (.block (copyPt K.M.n K.E K.D))

/-- The last iteration, `j = 0` (with `rbx = 1`): `R = 16 R` in Jacobian
coordinates, `R` and the entry into projective coordinates, and their sum by
the complete formulas. -/
def stepLast : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (quadJ K) <|
  .seq (toProjR K) <|
  .seq (.block ((tc K).digit ++ select K)) <|
  .seq (.block (tc K).negY) <|
  .seq (toProjE K) <|
  .seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))

/-- `[k]P` into `R`, for the table of the bits of `k + offset J` at `K.bits`
(`J ≥ 2`). -/
def windowJ : Prog isa :=
  .seq (buildJ K) <| .seq (.block (init K)) <| .seq (.loop (stepJ K) .ne) (stepLast K)

end WinCfg

end VG.Impl.Weierstrass.X86_64
