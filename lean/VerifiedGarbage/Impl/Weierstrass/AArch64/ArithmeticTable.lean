import VerifiedGarbage.Impl.Weierstrass.AArch64.ArithmeticAdd
import VerifiedGarbage.Impl.Weierstrass.AArch64.Naf

namespace VG.Impl.Weierstrass.AArch64.ArithmeticTable
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open Jacobian

def tableStep (K : WinCfg) : Prog isa :=
  .seq (ArithmeticAdd.add K K.R (Naf.twice K) K.D) <|
    .block (copyPt 4 K.R K.D ++ tableStore K ++
      ([.addImm .x .x20 .x20 96,decCounter] : List Instr))

def table (K : WinCfg) : Prog isa :=
  .seq (fprogB K.M (dblJMul K.S K.P K.D)) <|
  .seq (.block (copyPt 4 (Naf.twice K) K.D ++ copyPt 4 K.R K.P ++
    ([.addImm .x .x20 .x0 K.tbl] : List Instr) ++ tableStore K ++
    ([.addImm .x .x20 .x20 96,.movz .x .x19 7 0] : List Instr))) <|
  .loop (tableStep K) (.nonzero .x .x19)

end VG.Impl.Weierstrass.AArch64.ArithmeticTable
