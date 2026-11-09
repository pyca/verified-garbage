module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian

/-! Sparse signed digits for public P-256 verification scalars. -/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.Naf
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open Jacobian

/-- The cached double immediately follows the eight odd table entries. -/
def twice (K : WinCfg) : Pt := tablePt K 9

def digitRead (K : WinCfg) : List Instr :=
  [.add .x .x16 .x0 .x19,.ldrb .x2 .x16 K.bits]

/-- The signed byte's nonzero magnitude maps to one of the eight odd entries. -/
def digitIndex : List Instr :=
  [.lsr .x .x3 .x2 7,.lsl .x .x4 .x3 8,.sub .x .x2 .x2 .x4,
   .movz .x .x4 0 0,.sub .x .x3 .x4 .x3,.logic .eor .x .x2 .x2 .x3,
   .sub .x .x2 .x2 .x3,.addImm .x .x2 .x2 1,.lsr .x .x2 .x2 1]

def signRead (K : WinCfg) : List Instr :=
  [.add .x .x16 .x0 .x19,.ldrb .x3 .x16 K.bits,.lsr .x .x3 .x3 7]

end VG.Impl.Weierstrass.AArch64.Naf
