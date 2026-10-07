import VerifiedGarbage.Impl.Weierstrass.X86.TComb
import VerifiedGarbage.Impl.Weierstrass.JacMul

/-!
# Signed four-bit variable-base multiplication on 32-bit x86

Build [1..8]P in scratch memory. Each recoded digit uses four Jacobian
doublings, a constant-time scan of all eight projective points, conditional
negation, and a complete addition. The scalar is recoded by adding
`8 * ((16^J - 1) / 15)` before producing its table of bits.
-/

namespace VG.Impl.Weierstrass.X86

open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass

namespace WinCfg

variable (K : WinCfg) (wk : Nat)

/--`8 Σ_{j<J} 16^j`, the recoding's offset. -/
def offset (J : Nat) : Nat := 8 * ((16 ^ J - 1) / 15)

/-- `[m + 1]P = [m]P + P` for `m = 1 … i`. -/
def adds : Nat → Prog isa
  | 0 => .block []
  | i + 1 => .seq (adds i) (fprog K.M wk (rcb3 K.S (K.tblPt (i + 1)) (K.tblPt 1) (K.tblPt (i + 2))))

/-- The table: `[1]P = P`, then `[m + 1]P = [m]P + P`. -/
def build : Prog isa := .seq (.block (copyPt K.M.n (K.tblPt 1) K.P)) (adds K wk 7)

/-- The window method as the comb sees it, for the digits and their
negation: windows of 4 bits at `bits`. -/
def tc : TCombCfg where
  M := K.M
  wk := wk
  ptr := 0
  S := K.S
  A := K.R
  E := K.E
  D := K.D
  neg := K.neg
  zero := K.zero
  bits := K.bits
  kbytes := 4 * K.J
  tsym := ""
  w := 4
  J := K.J
  start := (0, 0)
  one := K.one

/-- Scan entries 1 through m, retaining the point selected by `ebx`. -/
def selectEntries : Nat → List Instr
  | 0 => []
  | m + 1 => selectEntries m ++ eqMask (m + 1) ++ selPt K.M.n K.E K.E (K.tblPt (m + 1))

/-- Start with infinity, then scan all eight points without secret addresses. -/
def select : List Instr :=
  setConst K.M.n K.E.x 0 ++ setConst K.M.n K.E.y K.one ++ setConst K.M.n K.E.z 0 ++
    selectEntries K 8

/-- The slots of zero, as a point (`toJ` and `fromJ` add zero to copy). -/
def zeroPt : Pt := ⟨K.zero, K.zero, K.zero⟩

/-- The mask `edx` of `[E.z] = 0` (all ones if it is). -/
def zeroMask : List Instr :=
  [.mov .edx (.mem (sc K.E.z))] ++
    ((List.range (2 * K.M.n - 1)).map fun j => .alu .or .edx (.mem (sc (K.E.z + 4 * (j + 1))))) ++
  [.alu .cmp .edx (.imm 1), .alu .sbb .edx (.reg .edx)]

/-- `R.y` = Montgomery's one where the mask `edx` is all ones, word `w`:
through `eax` and `ebx`. -/
def ySelWord (w : Nat) : List Instr :=
  [.mov .eax (.mem (sc (K.R.y + 4 * w))), .mov .ebx (.imm (BitVec.ofNat 32 (K.one / 2 ^ (32 * w)))), .alu .xor .ebx (.reg .eax),
    .alu .and .ebx (.reg .edx), .alu .xor .eax (.reg .ebx), .store (sc (K.R.y + 4 * w)) .eax]

/-- `R = (0 : 1 : 0)` where `E.z` is zero: `R.x` and `R.z` are zero then already. -/
def ySel : List Instr := zeroMask K ++ (List.range (2 * K.M.n)).flatMap (ySelWord K)

/-- For 256-bit fields, form `2YZ` directly: squaring and multiplication
use the same Montgomery kernel, so this saves two field subtractions. -/
def double (p o : Pt) : List FOp :=
  if K.M.n == 4 then dblJMul K.S p o else dblJ K.S p o

/-- Four Jacobiandoublings between E and D, bracketed by coordinate conversions. -/
def jac : Prog isa :=
  .seq (fprog K.M wk (toJ K.S K.R (zeroPt K) K.E)) <|
  .seq (fprog K.M wk (double K K.E K.D)) <|
  .seq (fprog K.M wk (double K K.D K.E)) <|
  .seq (fprog K.M wk (double K K.E K.D)) <|
  .seq (fprog K.M wk (double K K.D K.E)) <|
  fprog K.M wk (fromJ K.S K.E (zeroPt K) K.R)

/-- `R = 16 R`. -/
def quad : Prog isa := .seq (jac K wk) (.block (ySel K))

/-- Iteration `j = esi - 1` (with `esi` counting down from `J`):
`R = 16 R + [d_j]P`. -/
def step : Prog isa :=
  .seq (.block [.alu .sub .esi (.imm 1)]) <|
  .seq (quad K wk) <|
  .seq (.block ((tc K wk).digit ++ select K)) <|
  .seq (.block (tc K wk).negY) <|
  .seq (.seq (fprog K.M wk (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))) <|
  .block [.alu .test .esi (.reg .esi)]

/-- `R = O` and the counter. -/
def init : List Instr :=
  setConst K.M.n K.R.x 0 ++ setConst K.M.n K.R.y K.one ++ setConst K.M.n K.R.z 0 ++
    [.mov .esi (.imm (BitVec.ofNat 32 K.J))]

/-- `[k]P` into `R`, for the table of the bits of `k + offset J` at `K.bits`. -/
def window : Prog isa := .seq (build K wk) (.seq (.block (init K)) (.loop (step K wk) .ne))

end WinCfg

end VG.Impl.Weierstrass.X86
