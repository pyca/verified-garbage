import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedInputs

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PackedRoots packedSteps packedRunValues localOffset)

def productFiveCode : List Instr := (List.range 8).flatMap product++fiveCode

theorem productFive_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {zp : Nat → Nat → Nat → Int} {zl : Nat → Nat → Int}
    (hc : ProductConstants s) (hp : PackedRoots s zp)
    (hl : ∀i:Fin 7,RootReady s (localOffset i.val) (zl i.val))
    (hr : ∀j<8,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16 ∧
      ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j)) 16)
    (k : ∀t,VChg workRegs s t → Banks t (fun p =>
      Inverse.runValues zl 0 7 (packedRunValues (inputValues s p) zp packedSteps)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (productFiveCode++rest)) s Q := by
  simp only [productFiveCode,List.append_assoc]
  refine inputs_ok hc hr fun a ha _ va => ?_
  have ha' : VChg workRegs s a := ha.mono (by decide)
  refine five_ok va (packedRoots_frame hp ha') (fun i => (hl i).chg ha) fun t ht vt => ?_
  exact k t ((ha'.trans ht).mono (by simp)) vt

end VG.Proof.MlDsa.AArch64.Optimized.Paired
