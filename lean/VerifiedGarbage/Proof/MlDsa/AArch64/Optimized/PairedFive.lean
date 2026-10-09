import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStageRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPackedRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseLocalTable

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (packedSteps packedRunValues PackedRoots localOffset)

def fiveCode : List Instr := packedCode packedSteps++stageRunCode (fun i => localOffset i.val) (List.finRange 7)

theorem fiveCode_eq : fiveCode =
    ([1,2].flatMap fun len => (List.range 4).flatMap fun j =>
      rootPair ((if len=1 then 0 else 128)+32*j) ++
      [0,1].flatMap (fun p => packed (vr (8*p+2*j)) (vr (8*p+2*j+1)) len)) ++
    ([4,8,16].flatMap fun len => (List.range (16/len)).flatMap fun b =>
      rootPair ((if len=4 then 256 else if len=8 then 384 else 448)+32*b) ++
      (List.range (len/4)).flatMap (fun j => batchPair (b*len/2+j) (b*len/2+j+len/4))) := by
  decide +kernel

theorem five_ok {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    {zp : Nat → Nat → Nat → Int} {zl : Nat → Nat → Int}
    (hv : Banks s v) (hp : PackedRoots s zp)
    (hl : ∀i:Fin 7,RootReady s (localOffset i.val) (zl i.val))
    (k : ∀t,VChg workRegs s t →
      Banks t (fun p => Inverse.runValues zl 0 7 (packedRunValues (v p) zp packedSteps)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (fiveCode++rest)) s Q := by
  simp only [fiveCode,List.append_assoc]
  refine packedRun_ok packedSteps (by decide) hv hp fun a ha hpa va => ?_
  refine stageRun_ok (List.finRange 7) (fun i => localOffset i.val) (fun i => zl i.val)
    va (fun i => (hl i).chg ha) hpa.q fun t ht vt => ?_
  have hc : VChg workRegs s t := (ha.trans ht).mono (by
    intro r hr
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · exact hr
    · exact (show stageRunRegs⊆workRegs by decide) hr)
  exact k t hc (by simpa only [stageRunValues_all] using vt)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
