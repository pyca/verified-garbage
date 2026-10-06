import VerifiedGarbage.Impl.Weierstrass.JacMul
import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb

/-!
# Short Weierstrass curves on AArch64: scalar multiplication by windows

`[k]P` for a point `P` known only at run time and `k < 2^(64 n)`, by
signed 4-bit windows. The scalar is recoded as `k' = k + 8 Σ_{j<J} 16^j`
(`addConst`, `J = 16 n + 1` digits, so `k' < 16^J`), whose nibbles `k'_j`
give the digits `d_j = k'_j - 8 ∈ [-8, 7]` with `k = Σ_j d_j 16^j`. The
table `[m]P` for `m = 1 … 8` is built in the working space (`build`: `P`,
then seven complete additions); then, from `R = O`, for `j = J - 1` down
to `0`, `R = 16 R + [d_j]P`: four doublings (in Jacobian coordinates, `quad`), the
entry of `|d_j|` selected in
constant time and negated for a negative digit, and a complete addition. The
formulas are those for `a = -3` (`dblJ`, `rcb3`, with `b` in `S.b3`).

The digits are secret: every entry's every word is loaded and masked
(`selectWord`), the masks of the magnitudes as for the comb (`digit`), and
`y` negated by a mask of the digit's sign (`negY`). The counter `x19` is
public, as are every address and branch.
-/

namespace VG.Impl.Weierstrass.AArch64

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

namespace WinCfg

variable (K : WinCfg)

/-- `8 Σ_{j<J} 16^j`, the recoding's offset. -/
def offset (J : Nat) : Nat := 8 * ((16 ^ J - 1) / 15)

/-- `[dst] = [src] + c`, `n + 1` words from `n` (`c < 2^(64 (n + 1))`): `c` to
`dst`, then the carry chain of `src` (with a top word of zero) and `dst`, in the
registers `low n` and `top n`. -/
def addConst (n src dst c : Nat) : List Instr :=
  setConst (n + 1) dst c ++ loads (low n) src ++ [.movz .x (top n) 0 0] ++
    chain (.adds .x) (.adcs .x) (low n ++ [top n]) dst ++ stores (low n ++ [top n]) dst

/-- `[m + 1]P = [m]P + P` for `m = 1 … i`. -/
def adds : Nat → Prog isa
  | 0 => .block []
  | i + 1 => .seq (adds i) (fprogB K.M (rcb3 K.S (K.tblPt (i + 1)) (K.tblPt 1) (K.tblPt (i + 2))))

/-- The table: `[1]P = P`, then `[m + 1]P = [m]P + P`. -/
def build : Prog isa := .seq (.block (copyPt K.M.n (K.tblPt 1) K.P)) (adds K 7)

/-- `x4 |= [x0 + d] & mask m`, through `x9` and `x2`. -/
def loadCand (d m : Nat) : List Instr :=
  [ld .x9 d, .logic .and .x .x2 .x9 (maskReg m), .logic .orr .x .x4 .x4 .x2]

/-- Word `w` of coordinate `c` (`0`, `1`, `2` for `X`, `Y`, `Z`) of the entry of
the magnitude whose mask is all ones, into `[o + 8 w]`: `(0 : R : 0)` for `0`. -/
def selectWord (c o w : Nat) : List Instr :=
  [.movz .x .x4 0 0] ++
    (if c = 1 then const64 .x9 (wordOf K.one w) ++ [.logic .and .x .x4 .x9 (maskReg 0)] else []) ++
    ((List.range 8).flatMap fun i =>
      loadCand (K.tbl + 24 * K.M.n * i + 8 * K.M.n * c + 8 * w) (i + 1)) ++
    [st .x4 (o + 8 * w)]

/-- The entry for the magnitude whose mask is all ones, into `E`. -/
def select : List Instr :=
  (List.range K.M.n).flatMap (selectWord K 0 K.E.x) ++
  (List.range K.M.n).flatMap (selectWord K 1 K.E.y) ++
  (List.range K.M.n).flatMap (selectWord K 2 K.E.z)

/-- The slots of zero, as a point (`toJ` and `fromJ` add zero to copy). -/
def zeroPt : Pt := ⟨K.zero, K.zero, K.zero⟩

/-- `R.y` = Montgomery's one where the mask `x2` is all ones, word `w`: through
`x4` and `x9`. -/
def ySelWord (w : Nat) : List Instr :=
  [ld .x9 (K.R.y + 8 * w), .bicRor .x .x9 .x9 .x2 0] ++ const64 .x4 (wordOf K.one w) ++
    [.logic .and .x .x4 .x4 .x2, .logic .orr .x .x4 .x4 .x9, st .x4 (K.R.y + 8 * w)]

/-- `R = (0 : 1 : 0)` where `E.z` is zero: `R.x` and `R.z` are zero then already. -/
def ySel : List Instr := zeroMask K.M.n K.E.z ++ (List.range K.M.n).flatMap (ySelWord K)

/-- Four-word fields use direct `2YZ` while its squares use the general multiplier. -/
def double (p o : Pt) : List FOp :=
  if K.M.n == 4 then dblJMul K.S p o else dblJ K.S p o

/-- `R = 16 R` but where it is `O`: into Jacobian coordinates in `E`, four
doublings between `E` and `D`, and back. -/
def jac : Prog isa :=
  .seq (fprogB K.M (toJ K.S K.R (zeroPt K) K.E)) <|
  .seq (fprogB K.M (double K K.E K.D)) <| .seq (fprogB K.M (double K K.D K.E)) <|
  .seq (fprogB K.M (double K K.E K.D)) <| .seq (fprogB K.M (double K K.D K.E)) <|
  fprogB K.M (fromJ K.S K.E (zeroPt K) K.R)

/-- `R = 16 R`. -/
def quad : Prog isa := .seq (jac K) (.block (ySel K))

/-- Iteration `j = x19 - 1`: `R = 16 R + [d_j]P`. -/
def step : Prog isa :=
  .seq (.block [decCounter]) <|
  .seq (quad K) <|
  .seq (.block (digit K.bits ++ select K ++ negY K.M K.neg K.zero K.E.y K.bits)) <|
  .seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) <|
  .block (copyPt K.M.n K.R K.D)

/-- `R = O` and the counter. -/
def init : List Instr :=
  setConst K.M.n K.R.x 0 ++ setConst K.M.n K.R.y K.one ++ setConst K.M.n K.R.z 0 ++
    [.movz .x .x19 (BitVec.ofNat 16 K.J) 0]

/-- `[k]P` into `R`, for the table of the bits of `k + offset J` at `K.bits`. -/
def window : Prog isa := .seq (build K) (.seq (.block (init K)) (.loop (step K) (.nonzero .x .x19)))

end WinCfg

end VG.Impl.Weierstrass.AArch64
