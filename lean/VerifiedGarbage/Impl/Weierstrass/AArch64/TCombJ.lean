module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.TComb

/-!
# Fixed-base Booth comb with Jacobian mixed additions

The scalar bits and affine tables have the same layout as `TComb`. Booth
windows are processed from low to high, starting with the first selected
point and accumulating with `maddJ`. The intended arithmetic contract excludes
equal nonzero input points using the bound on the sum of all lower windows;
it also requires at least two windows and a clear top carry bit.

Every table entry is read in fixed order by the existing secret `select`.
Sign, zero-digit and infinity corrections use masks, with no secret branch
or secret address. Only the public window counter controls the loop.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64
open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

/-- `x3` is all ones iff the `n` words at `z` are not all zero. -/
def nzMask (n z : Nat) : List Instr :=
  [zero7,ld .x1 z] ++ (List.range (n-1)).flatMap (fun i =>
    [ld .x2 (z+8*(i+1)),.logic .orr .x .x1 .x1 .x2]) ++
  [.subs .x .x16 .x7 .x1,.sbc .x .x3 .x7 .x7]

namespace TCombCfg
variable (K : TCombCfg)

/-- Booth magnitude in `x2`: for window `W`, preceding bit `c` and
window-top bit `s`, `abs(W+c-2^w*s)`. Window zero omits the preceding bit. -/
def bdigit (carry : Bool) : List Instr :=
  winIndex K.w ++ hornerBits K.bits K.w ++
  (if carry then [.ldrb .x4 .x16 (K.bits-1),.add .x .x2 .x2 .x4] else []) ++
  [zero7,.ldrb .x4 .x16 (K.bits+K.w-1),.sub .x .x3 .x7 .x4,
    .logic .eor .x .x2 .x2 .x3,.sub .x .x2 .x2 .x3] ++
  const64 .x9 (BitVec.ofNat 64 (2^K.w)) ++
  [.logic .and .x .x3 .x3 .x9,.add .x .x2 .x2 .x3]

/-- `x3` is minus the top bit of the current window. -/
def bsignMask : List Instr :=
  winIndex K.w ++ [zero7,.ldrb .x4 .x16 (K.bits+K.w-1),.sub .x .x3 .x7 .x4]

/-- Negate the selected ordinate under the Booth sign mask. -/
def bnegY : List Instr :=
  Mont.AArch64.sub K.M K.neg K.zero K.E.y ++ K.bsignMask ++ sel K.M.n K.E.y K.E.y K.neg

/-- Clear padding bits up to the end of the last window, in whole words. -/
def clearBits : List Instr :=
  zero7 :: (List.range ((K.w*K.J-K.kbytes+7)/8)).map
    (fun i => st .x7 (K.bits+K.kbytes+8*i))

/-- Initialize the accumulator from window zero and set the next window to one. -/
def first : Prog isa :=
  .seq (.block (K.clearBits ++ [.movz .x .x19 0 0] ++ K.bdigit false ++ K.select)) <|
  .seq (.block K.bnegY) <|
  .block (copyPt K.M.n K.A K.E ++ [.movz .x .x19 1 0])

/-- One public window: add its signed entry, correct an infinite accumulator,
and retain the accumulator for a zero digit. `x4 = x19-J` is zero after the final window. -/
def stepJWith (arithmetic : Mod → List FOp → Prog isa) : Prog isa :=
  .seq (.block (K.bdigit true ++ K.select)) <|
  .seq (.block K.bnegY) <|
  .seq (arithmetic K.M (maddJ K.S K.A K.E K.D)) <|
  .seq (.block (nzMask K.M.n K.A.z ++ selPt K.M.n K.D K.E K.D)) <|
  .block (K.bdigit true ++ [zero7,.movz .x .x5 1 0,.subs .x .x16 .x2 .x5,
    .sbc .x .x3 .x7 .x7] ++ selPt K.M.n K.A K.D K.A ++
    [.addImm .x .x19 .x19 1,.subImm .x .x4 .x19 K.J])

/-- The baseline field compiler includes the specialized P-256 squaring path. -/
def stepJ : Prog isa := K.stepJWith fprogB

/-- Normalize infinity's ordinate to Montgomery one, retaining finite ordinates. -/
def outFix : List Instr :=
  nzMask K.M.n K.A.z ++ sel K.M.n K.A.y K.zero K.A.y ++
  [.subImm .x .x4 .x7 1,.logic .eor .x .x3 .x3 .x4] ++
  (List.range K.M.n).flatMap fun i =>
    const64 .x1 (wordOf K.one i) ++
    [.logic .and .x .x1 .x1 .x3,ld .x2 (K.A.y+8*i),
      .logic .orr .x .x1 .x1 .x2,st .x1 (K.A.y+8*i)]

/-- Convert the Jacobian accumulator to homogeneous coordinates `(XZ,Y,Z³)`. -/
def outOps : List FOp :=
  [.mul K.A.x K.A.x K.A.z,.mul K.S.t0 K.A.z K.A.z,.mul K.A.z K.S.t0 K.A.z]

/-- Experimental arithmetic injection changes field schedules only. -/
def combJWith (arithmetic : Mod → List FOp → Prog isa) : Prog isa :=
  .seq K.first <| .seq (.loop (K.stepJWith arithmetic) (.nonzero .x .x4)) <|
    .seq (.block K.outFix) (arithmetic K.M K.outOps)

/-- Secret-scalar fixed-base multiplication with Booth digits. -/
def combJ : Prog isa := K.combJWith fprogB

end TCombCfg
end VG.Impl.Weierstrass.AArch64
