module

public import VerifiedGarbage.Impl.P256.VerifyDouble
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian

/-! Sparse signed digits for public P-256 verification scalars. -/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.Naf
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open Jacobian

/-- The cached double immediately follows the eight odd table entries. -/
def twice (K : WinCfg) : Pt := tablePt K 9

/-- Register forwarding is restricted to the measured P-256 verification layouts. -/
def double (K : WinCfg) (p o : Pt) : Prog isa := VG.Impl.P256.VerifyDouble.double K.M K.S p o

def tableStep (K : WinCfg) : Prog isa :=
  .seq (jacAdd K K.R (twice K) K.D) <|
    .block (copyPt 4 K.R K.D ++ tableStore K ++
      ([.addImm .x .x20 .x20 96,decCounter] : List Instr))

def table (K : WinCfg) : Prog isa :=
  .seq (fprogB K.M (dblJMul K.S K.P K.D)) <|
  .seq (.block (copyPt 4 (twice K) K.D ++ copyPt 4 K.R K.P ++
    ([.addImm .x .x20 .x0 K.tbl] : List Instr) ++ tableStore K ++
    ([.addImm .x .x20 .x20 96,.movz .x .x19 7 0] : List Instr))) <|
  .loop (tableStep K) (.nonzero .x .x19)

def digitRead (K : WinCfg) : List Instr :=
  [.add .x .x16 .x0 .x19,.ldrb .x2 .x16 K.bits]

/-- The signed byte's nonzero magnitude maps to one of the eight odd entries. -/
def digitIndex : List Instr :=
  [.lsr .x .x3 .x2 7,.lsl .x .x4 .x3 8,.sub .x .x2 .x2 .x4,
   .movz .x .x4 0 0,.sub .x .x3 .x4 .x3,.logic .eor .x .x2 .x2 .x3,
   .sub .x .x2 .x2 .x3,.addImm .x .x2 .x2 1,.lsr .x .x2 .x2 1]

def signRead (K : WinCfg) : List Instr :=
  [.add .x .x16 .x0 .x19,.ldrb .x3 .x16 K.bits,.lsr .x .x3 .x3 7]

def signedEntry (K : WinCfg) : Prog isa :=
  .seq (.block (digitIndex ++ publicEntry K)) <|
    .seq (.block (signRead K)) <|
      .ite (.nonzero .x .x3) (.block (Mont.AArch64.sub K.M K.E.y K.zero K.E.y)) (.block [])

def digit (K : WinCfg) : Prog isa :=
  .seq (.block (digitRead K)) <|
    .ite (.nonzero .x .x2)
      (.seq (signedEntry K) <|
        .seq (jacAdd K K.R K.E K.D) (.block (copyPt 4 K.R K.D))) (.block [])

def step (K : WinCfg) : Prog isa :=
  .seq (.block [decCounter]) <|
    .seq (double K K.R K.D) <| .seq (.block (copyPt 4 K.R K.D)) (digit K)

def window (K : WinCfg) : Prog isa :=
  .seq (table K) <|
  .seq (.block (infinity K K.R ++ ([.movz .x .x19 256 0] : List Instr))) <|
  .seq (digit K) <|
  .seq (.loop (step K) (.nonzero .x .x19)) (jacFinish K)

end VG.Impl.Weierstrass.AArch64.Naf
