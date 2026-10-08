import VerifiedGarbage.Impl.P256.EcdhJac.Base
import VerifiedGarbage.Impl.P256.EcdhTable
import VerifiedGarbage.Impl.P256.EcdhInverse
import VerifiedGarbage.Impl.P256.EcdhDouble

namespace VG.Impl.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64


 /-- Register forwarding preserves the table formulas’ field-operation order. -/
def arithmetic (ops : List FOp) : Prog isa :=
  .block (Forward.optimize (fprog K.M ops))

def buildStep : Prog isa :=
  .seq (.block [.addImm .x .x19 .x19 1]) <|
  .seq (EcdhTable.program false) <|
  .block (storeEntry ++ [.subImm .x .x4 .x19 16])
def build : Prog isa :=
  .seq (.block (copyPt 4 K.E K.P ++ copy 4 z2 K.P.z ++ copy 4 zz K.P.z ++
    [.movz .x .x19 1 0] ++ storeEntry)) <|
  .seq (EcdhTable.program true) <|
  .seq (.block (copy 4 K.D.x K.S.t3 ++ copy 4 K.D.y K.S.t2 ++
    [.movz .x .x19 2 0] ++ storeEntry)) <|
  .loop (buildStep) (.nonzero .x .x4)

def double : Prog isa := EcdhDouble.program
def add : Prog isa :=
  .seq (VerifyAllocated.program .cachedHead) (VerifyAllocated.program .jacTail)
def dblStep : Prog isa :=
  .seq (double) (.block [.subImm .x .x19 .x19 2048,.lsr .x .x4 .x19 11])
def dbls : Prog isa :=
  .seq (.block [.movz .x .x4 10240 0,.add .x .x19 .x19 .x4])
    (.loop (dblStep) (.nonzero .x .x4))

def step : Prog isa :=
  .seq (.block [decCounter]) <| .seq (dbls) <|
  .seq (.block (tc.digit ++ select ++ negYW K.M 5 K.neg K.zero K.E.y K.bits)) <|
  .seq (add) <|
  .block (nzMask 4 K.R.z ++ selPt 4 K.D K.E K.D ++ tc.digit ++
    [zero7,.movz .x .x5 1 0,.subs .x .x16 .x2 .x5,.sbc .x .x3 .x7 .x7] ++
    selPt 4 K.R K.D K.R)
def first : List Instr :=
  [.movz .x .x19 51 0] ++ tc.digit ++ select ++ negYW K.M 5 K.neg K.zero K.E.y K.bits ++ copyPt 4 K.R K.E

def window : Prog isa :=
  .seq (build) <| .seq (.block (first)) <|
  .seq (.loop (step) (.nonzero .x .x19)) <|
  .seq (.block tc.outFix) (arithmetic tc.outOps)

def prep : Prog isa :=
  .seq (.block (WinCfg.addConst 4 (c.sl VG.Impl.Ecdsa.AArch64.K) c.winK (16*((32^52-1)/31))))
    (bits c.winK c.winBits 40)

/-- x20 retains the output pointer across the allocator; four additional ABI
registers are saved separately from its spill area7104..7679. -/
def extra : List (Reg × Nat) := [(.x26,7800),(.x27,7808),(.x28,7816),(.x30,7824),(.x20,7832)]
def wrappedWindow : Prog isa :=
  .seq (.block (extra.map fun (r,d) => st r d)) <|
  .seq (window) (.block (extra.map fun (r,d) => ld r d))

def exchange : Prog isa :=
  .seq (.block VG.Impl.Ecdh.AArch64.Cfg.args) <|
  .seq (.block (c.setupWith none)) <|
  .seq (.block (VG.Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (VG.Impl.Ecdh.AArch64.Cfg.validate c) <| .seq prep <|
  .seq (wrappedWindow) <|
  .seq EcdhInverse.inverse (VG.Impl.Ecdh.AArch64.Cfg.middle c)
end VG.Impl.P256.EcdhJac
