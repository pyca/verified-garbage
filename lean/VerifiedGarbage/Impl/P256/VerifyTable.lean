module

public import VerifiedGarbage.Impl.P256.EcdhTable
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint

/-! The odd multiples `Q, 3Q, …, 15Q` of public P-256 verification by co-Z
arithmetic: ECDH's DBLU gives `2Q` and `Q` at one `Z`; with `2Q` as the
co-Z addend, each of ECDH's ZADDU steps adds `2Q`, returning the next odd
multiple, `2Q` rescaled to its `Z`, and that `Z`'s square and cube. Entry `a`
is stored at `tablePt K a`, its `Z²` and `Z³` at `tableZ2 (a-1)` and
`tableZ3 (a-1)`; `2Q` ends in entry 9, as `ArithmeticTable.table` leaves it. -/

@[expose] public section

namespace VG.Impl.P256.VerifyTable
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open Jacobian

def K := VG.Impl.Ecdsa.Verify.AArch64.P256Joint.cfg.K
def z2 : Nat := EcdhJac.z2
def zz : Nat := EcdhJac.zz

/-- `x16`: entry `x19`'s point. -/
def entryAddr : List Instr :=
  [.subImm .x .x1 .x19 1,.movz .x .x2 96 0,.mul .x .x1 .x1 .x2,
   .addImm .x .x16 .x0 K.tbl,.add .x .x16 .x16 .x1]

/-- `x16`: entry `x19`'s cached powers, `tableZ2 (x19-1)`. -/
def cacheAddr : List Instr :=
  [.subImm .x .x1 .x19 1,.lsl .x .x1 .x1 6,.movz .x .x2 6000 0,
   .add .x .x16 .x0 .x2,.add .x .x16 .x16 .x1]

/-- Store the co-Z point `E` and the powers of its `Z` as entry `x19`. -/
def storeEntry : List Instr :=
  entryAddr ++ (List.range 12).flatMap (fun i => [ld .x1 (K.E.x+8*i),.str .x .x1 .x16 (8*i)]) ++
  cacheAddr ++ (List.range 8).flatMap (fun i => [ld .x1 (z2+8*i),.str .x .x1 .x16 (8*i)])

/-- `E = Q` (affine) with `Z² = Z³ = 1`, stored as entry 1. -/
def start : List Instr :=
  copyPt 4 K.E K.P ++ copy 4 z2 K.P.z ++ copy 4 zz K.P.z ++ [.movz .x .x19 1 0] ++ storeEntry

/-- After DBLU (`E = 2Q`, `(t3, t2)` = `Q` at its `Z`): the addend `D = 2Q`, `E = Q`. -/
def swap : List Instr :=
  copy 4 K.D.x K.E.x ++ copy 4 K.D.y K.E.y ++ copy 4 K.E.x K.S.t3 ++ copy 4 K.E.y K.S.t2

def step : Prog isa :=
  .seq (.block [.addImm .x .x19 .x19 1]) <|
  .seq (EcdhTable.program false) <|
  .block (storeEntry ++ ([.subImm .x .x4 .x19 8] : List Instr))

/-- `2Q` at the last `Z` into entry 9 and `D`, and `R` a copy of `E`. -/
def finish : List Instr :=
  copy 4 (tablePt K 9).x K.D.x ++ copy 4 (tablePt K 9).y K.D.y ++ copy 4 (tablePt K 9).z K.E.z ++
  copy 4 K.D.z K.E.z ++ copyPt 4 K.R K.E

def build : Prog isa :=
  .seq (.block start) <| .seq (EcdhTable.program true) <|
  .seq (.block swap) <| .seq (.loop step (.nonzero .x .x4)) (.block finish)

end VG.Impl.P256.VerifyTable
