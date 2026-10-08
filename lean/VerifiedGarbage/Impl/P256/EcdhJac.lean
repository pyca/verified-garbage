import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Impl.P256.VerifyAllocated
import VerifiedGarbage.Impl.P256.EcdhSelect

/-! Secret-scalar width-five Jacobian/co-Z ECDH.
All scans use fixed addresses and all control flow uses public counters. -/
namespace VG.Impl.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64

def c := p256
def K : WinCfg := { c.winCfg VG.Impl.Ecdh.AArch64.PX VG.Impl.Ecdh.AArch64.PY with J:=52, tbl:=2816 }
def z2 : Nat := 5400
def zz : Nat := 5432
def tc : TCombCfg := ⟨K.M,K.S,K.R,K.E,K.D,K.neg,K.zero,K.bits,260,"",5,52,(0,0),K.one⟩
def selectedWord (i : Nat) : Nat := if i<12 then K.E.x+8*i else z2+8*(i-12)

def select : List Instr := EcdhSelect.neon K.tbl K.E.x z2

def entryAddr : List Instr :=
  [.subImm .x .x1 .x19 1,.movz .x .x2 160 0,.mul .x .x1 .x1 .x2,
   .addImm .x .x16 .x0 K.tbl,.add .x .x16 .x16 .x1]
def storeEntry : List Instr := entryAddr ++ (List.range 20).flatMap fun i =>
  [ld .x1 (selectedWord i),.str .x .x1 .x16 (8*i)]

def dbluOps : List FOp :=
  [.mul K.S.t0 K.P.x K.P.x, .mul K.S.t1 K.P.y K.P.y, .mul K.S.t2 K.S.t1 K.S.t1,
   .mul K.S.t3 K.P.x K.S.t1, .add K.S.t3 K.S.t3 K.S.t3, .add K.S.t3 K.S.t3 K.S.t3,
   .sub K.S.t4 K.S.t0 K.P.z, .add K.S.t5 K.S.t4 K.S.t4, .add K.S.t4 K.S.t5 K.S.t4,
   .mul K.E.x K.S.t4 K.S.t4, .sub K.E.x K.E.x K.S.t3, .sub K.E.x K.E.x K.S.t3,
   .sub K.S.t5 K.S.t3 K.E.x, .mul K.E.y K.S.t4 K.S.t5,
   .add K.S.t2 K.S.t2 K.S.t2, .add K.S.t2 K.S.t2 K.S.t2, .add K.S.t2 K.S.t2 K.S.t2,
   .sub K.E.y K.E.y K.S.t2, .add K.E.z K.P.y K.P.y,
   .mul z2 K.E.z K.E.z, .mul zz z2 K.E.z]

def zadduOps : List FOp :=
  [.sub K.S.t0 K.D.x K.E.x, .mul K.S.t1 K.S.t0 K.S.t0, .mul K.E.z K.E.z K.S.t0,
   .mul K.D.x K.D.x K.S.t1, .mul K.S.t3 K.E.x K.S.t1, .sub K.S.t4 K.D.y K.E.y,
   .mul K.S.t5 K.S.t4 K.S.t4, .sub K.S.t2 K.D.x K.S.t3, .mul K.D.y K.D.y K.S.t2,
   .sub K.E.x K.S.t5 K.D.x, .sub K.E.x K.E.x K.S.t3, .sub K.E.y K.D.x K.E.x,
   .mul K.E.y K.S.t4 K.E.y, .sub K.E.y K.E.y K.D.y,
   .mul z2 z2 K.S.t1, .mul zz z2 K.E.z]


 /-- Register forwarding preserves the table formulas’ field-operation order. -/
def arithmetic (ops : List FOp) : Prog isa :=
  .block (Forward.optimize (fprog K.M ops))

def buildStep : Prog isa :=
  .seq (.block [.addImm .x .x19 .x19 1]) <|
  .seq (arithmetic zadduOps) <|
  .block (storeEntry ++ [.subImm .x .x4 .x19 16])
def build : Prog isa :=
  .seq (.block (copyPt 4 K.E K.P ++ copy 4 z2 K.P.z ++ copy 4 zz K.P.z ++
    [.movz .x .x19 1 0] ++ storeEntry)) <|
  .seq (arithmetic dbluOps) <|
  .seq (.block (copy 4 K.D.x K.S.t3 ++ copy 4 K.D.y K.S.t2 ++
    [.movz .x .x19 2 0] ++ storeEntry)) <|
  .loop (buildStep) (.nonzero .x .x4)

def double : Prog isa := VerifyAllocated.program .doubleRR
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
  .seq (VG.Impl.Ecdh.AArch64.Cfg.prefix' c) <|
  .seq (.block (VG.Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (VG.Impl.Ecdh.AArch64.Cfg.validate c) <| .seq prep <|
  .seq (wrappedWindow) <|
  .seq c.pPow (VG.Impl.Ecdh.AArch64.Cfg.middle c)
end VG.Impl.P256.EcdhJac
