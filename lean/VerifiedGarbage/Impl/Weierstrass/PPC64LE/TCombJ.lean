module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TComb

/-!
# `[k]G` by a fixed-base Booth comb with Jacobian mixed additions, on PPC64LE

AArch64's `TCombJ` (`Impl/Weierstrass/AArch64/TCombJ.lean`) on PPC64LE's
comb (`Impl/Weierstrass/PPC64LE/TComb.lean`): the same table (row `j` holds
`[m 2^(w j)]G` for `m = 1 … H`, `H = 2^(w-1)`, affine, in Montgomery's form)
and the same scan of a row, but Booth's digits
`d_j = W_j + c_j - 2^w s_j` of the scalar's windows `W_j` (`w` bits), `c_j`
the bit below window `j` (none for `j = 0`) and `s_j` the window's top bit,
taken from the low window up, so that `[k]G = Σ_j [d_j 2^(w j)]G`
(`Proof/Weierstrass/Booth.lean`), with the last window short (`topBits < w`,
its top bit clear). The sum is kept in Jacobian coordinates in the ladder's
`R`, and each window's entry added by the mixed addition `maddJ`
(`Impl/Weierstrass/Slots.lean`), a call of the point function
`vg_<curve>_point_madd`. The mixed addition fails for equal points, which
the digits' bound excludes (`booth_ne`), and for `R = O`, so:

1. `R` = window 0's entry (`O`, `Z = 0`, for a zero digit);
2. for `j` from 1 to `J - 1` (`r31 = j`): the entry `E` of digit `d_j` into
   the point functions' `Q` (`|d_j|`'s entry of row `j`, `y` negated for a
   negative digit, `Q = (0 : 1 : 0)` for a zero one), `D = R + E` by
   `maddJ`, then `D = E` if `R = O` (its `Z` is zero), and `R = D` unless
   the digit is zero;
3. `R`'s `Z` zero (`O`) gets `Y = 1`, and `R` goes to homogeneous
   coordinates, `(X Z : Y : Z³)` (`fromJ`, with `Z²` in `-y`'s slot).

Every choice is by a mask, and the only branches are on the public counter
`r31`: only the pointers may affect timing.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

open VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Mont.PPC64LE
open Point

namespace TCombCfg

variable (K : TCombCfg)

/-- `r7 = 1` if window `r31`'s top bit is set (`W ≥ H`), else `0`: always
`0` for the last, short, window. -/
def topBit : List Instr := [.lbz .r7 .r4 (K.L.bits + K.w - 1)]

/-- Booth's digit of window `r31`: `r9 = |W + c - 2^w s|`, `c` the bit
below the window (if `carry`), `s` its top bit, through `r4`–`r7`. -/
def bdigit (carry : Bool) : Prog isa :=
  .seq (.block K.windowIndex) <|
  .seq (.block K.lastTest) <|
  .seq (.ite isLast (.block (K.horner K.topBits ++ [.li .r7 0])) (.block (K.horner K.w ++ K.topBit))) <|
  .block ((if carry then [.lbz .r5 .r4 (K.L.bits - 1), .add .r9 .r9 .r5] else []) ++
    [.li .r5 0, .sub .r5 .r5 .r7, .li .r6 (2 ^ K.w), .logic .and .r6 .r6 .r5,
      .sub .r9 .r9 .r6, .logic .xor .r9 .r9 .r5, .sub .r9 .r9 .r5])

/-- The mask `r10` of a negative digit: `-s`, `0` for the last window. -/
def bsign : Prog isa :=
  .seq (.block K.lastTest) <|
  .ite isLast (.block [.li .r10 0])
    (.block (K.windowIndex ++ [.lbz .r4 .r4 (K.L.bits + K.w - 1), .li .r10 0, .sub .r10 .r10 .r4]))

/-- The signed entry of window `r31` into `Q`. -/
def bentry (carry : Bool) : Prog isa :=
  .seq (K.bdigit carry) <| .seq K.select <|
  .seq (subCall K.F K.neg K.zero K.Q.y) <|
  .seq K.bsign (.block (sel K.L.M.n K.Q.y K.Q.y K.neg))

/-- The mask `r10 = -(x ≠ 0)` of `x` in `r`: `0 - x` borrows (`CA = 0`)
exactly for `x ≠ 0`, and `r10 - r10 - 1 + CA` is `CA - 1`. Through `r5`. -/
def nzOf (r : Reg) : List Instr := [.li .r5 0, .subc .r5 .r5 r, .sube .r10 .r10 .r10]

/-- The mask `r10` of `R`'s `Z` being nonzero (`R ≠ O`), through `r4`, `r5`. -/
def zMask : List Instr :=
  [.load .d .r4 wb K.L.R.z] ++ (List.range (K.L.M.n - 1)).flatMap (fun i =>
    [.load .d .r5 wb (K.L.R.z + 8 * (i + 1)), .logic .or .r4 .r4 .r5]) ++ nzOf .r4

/-- The point function of the mixed addition, `O = P + Q` for a Jacobian `P`
and an affine `Q`. -/
def maddName : String := s!"vg_{K.F.curve}_point_madd"

/-- A call of it. -/
def maddCall : Prog isa := .call K.maddName (fnOps K.F false (maddJ sId pId qId oId))

/-- Window `r31 + 1`: its entry, `D = R + E`, `D = E` if `R = O`, `R = D`
unless the digit is zero, and `r6 = r31 - (J - 1)`. -/
def bstep : Prog isa :=
  .seq (.block [.addi .r31 .r31 1]) <|
  .seq (K.bentry true) <|
  .seq (.block (copyPt K.L.M.n K.P K.L.R)) <|
  .seq K.maddCall <|
  .seq (.block (K.zMask ++ selPt K.L.M.n K.O K.Q K.O)) <|
  .seq (K.bdigit true) <|
  .block (nzOf .r9 ++ selPt K.L.M.n K.L.R K.L.R K.O ++ K.lastTest)

/-- `R = O`'s `Y` set to one, and `R` to homogeneous coordinates, with `Z²`
in `-y`'s slot. -/
def bout : Prog isa :=
  .seq (.block (K.zMask ++ setConst K.L.M.n K.Q.y K.one ++ sel K.L.M.n K.L.R.y K.Q.y K.L.R.y)) <|
    fprog K.F (fromJ { K.L.S with t0 := K.neg } K.L.R ⟨K.zero, K.zero, K.zero⟩ K.L.R)

/-- The comb: `a` and `3b` to the point functions' slots, `R` = window 0's
entry, the windows `1 … J - 1`, and `R` to homogeneous coordinates. -/
def combJ : Prog isa :=
  .seq (.block (ladderSetup K.L ++ [.li .r31 0])) <|
  .seq (K.bentry false) <|
  .seq (.block (copyPt K.L.M.n K.L.R K.Q)) <|
  .seq (.loop K.bstep (.nonzero .d .r6)) K.bout

end TCombCfg

end VG.Impl.Weierstrass.PPC64LE
