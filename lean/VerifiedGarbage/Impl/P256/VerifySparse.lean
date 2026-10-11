module

public import VerifiedGarbage.Impl.P256.VerifyArithmetic

/-! Canonical field arithmetic specialized to the P-256 prime's sparse words. -/

@[expose] public section

namespace VG.Impl.P256.VerifySparse
open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64

def M := VerifyDouble.M

/-- Subtract the prime from a value below twice the prime. Its low word is
all ones and its third word is zero. The carry includes the extra high word. -/
def correct (ts : List Reg) (top : Reg) : List Instr :=
  ([.movz .x .x2 1 0,.adds .x .x1 ts[0]! .x2,
   ld .x2 (M.mo+8),.sbcs .x .x3 ts[1]! .x2,
   .sbcs .x .x4 ts[2]! .x7,ld .x2 (M.mo+24),.sbcs .x .x5 ts[3]! .x2,
   .sbcs .x .x2 top .x7] : List Instr) ++ selectsR ts (dRegs 4)

/-- Add the prime under the borrow mask, using its exact four words. -/
def sub (o a b : Nat) : List Instr :=
  zero7 :: loads (low 4) a ++ chain (.subs .x) (.sbcs .x) (low 4) b ++
  ([.sbc .x .x17 .x7 .x7,.lsr .x .x1 .x17 32,
   .lsl .x .x2 .x17 32,.sub .x .x2 .x2 .x17,
   .adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,
   .adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2] : List Instr) ++ stores (low 4) o

def op : FOp → List Instr
  | .sub o a b => sub o a b
  | f =>
    let o := match f with | .mul o _ _ | .add o _ _ | .sub o _ _ => o
    let (ts,top) := match f with
      | .mul _ a b => if a == b then ([Reg.x8,.x9,.x10,.x11],Reg.x12)
        else ((List.range 4).map (win 4 4),win 4 4 4)
      | _ => (low 4,VG.Impl.Mont.AArch64.top 4)
    let raw := opCode M f
    let suffix := csubR M ts top ++ stores ts o
    raw.take (raw.length-suffix.length) ++ correct ts top ++ stores ts o

end VG.Impl.P256.VerifySparse
