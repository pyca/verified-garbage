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

end VG.Impl.P256.EcdhJac
