import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedScaleBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawFinalSlice

/-! ## From `PairedScaleRun.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def scaleRunCode (js : List (Fin 4)) : List Instr := js.flatMap scaleStep

def scaleRunValues (v : Vector (BitVec 128) 8) : List (Fin 4) → Vector (BitVec 128) 8
  | [] => v
  | j::js => scaleRunValues (scaleOne v j) js

theorem scaleRun_ok (js : List (Fin 4)) {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Values} (hv : Banks s v)
    (hz : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 16382)
    (hb : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal 16382))
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg groupRegs s t → Banks t (fun p => scaleRunValues (v p) js) →
      WP isa (.block rest) t Q) :
    WP isa (.block (scaleRunCode js++rest)) s Q := by
  induction js generalizing s v with
  | nil => exact k s (VChg.refl _ _) hv
  | cons j js ih =>
    simp only [scaleRunCode,List.flatMap_cons,List.append_assoc]
    refine scaleBank_ok j hv hz hb hq fun a ha va => ?_
    have hsub : scaleClobs j⊆groupRegs := (show ∀j:Fin 4,scaleClobs j⊆groupRegs by decide) j
    have hc := ha.mono hsub
    refine ih va ?_ ?_ ?_ fun t ht vt => k t ((hc.trans ht).mono (by simp)) vt
    · rw [hc.get .v28 (by decide)]; exact hz
    · rw [hc.get .v29 (by decide)]; exact hb
    · rw [hc.get .v31 (by decide)]; exact hq

theorem scaleRunValues_all (v : Vector (BitVec 128) 8) :
    scaleRunValues v (List.finRange 4)=Inverse.scaleValues v := by
  have he (j : Fin 8) : (scaleRunValues v (List.finRange 4))[j.val]=(Inverse.scaleValues v)[j.val] := by
    fin_cases j <;> simp [scaleRunValues,scaleOne,Inverse.scaleValues,List.finRange_succ]
  exact Vector.ext fun j hj => he ⟨j,hj⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFinalArithmetic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def finalArithmetic : List Instr :=
  stageRunCode (fun i => 32*i.val) (List.finRange 7)++rootPair 224++scaleRunCode (List.finRange 4)

theorem finalArithmetic_eq : finalArithmetic=
    ([1,2,4].flatMap fun dist => (List.range (4/dist)).flatMap fun b =>
      rootPair (32*(8-(8/dist)+b)) ++
      (List.range dist).flatMap (fun j => batchPair (2*b*dist+j) (2*b*dist+j+dist))) ++
    rootPair 224 ++
    ((List.range 4).flatMap fun j =>
      [.vop (.sqdmulh .v24 (vr j) .v29),.vop (.sqdmulh .v25 (vr (8+j)) .v29),
       .vop (.mul (vr j) (vr j) .v28),.vop (.mul (vr (8+j)) (vr (8+j)) .v28),
       .vop (.mls (vr j) .v24 .v31),.vop (.mls (vr (8+j)) .v25 .v31)]) := by
  decide +kernel

theorem finalArithmetic_ok {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    (hv : Banks s v) (hr : ∀i:Fin 7,RootReady s (32*i.val) (Inverse.finalZ i.val))
    (hs : RootReady s 224 (fun _ => 16382))
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg stageRunRegs s t → Banks t (fun p => Inverse.rawFinalValues (v p)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (finalArithmetic++rest)) s Q := by
  simp only [finalArithmetic,List.append_assoc]
  refine stageRun_ok _ _ _ hv hr hq fun a ha va => ?_
  have hsa := hs.chg ha
  refine rootLoads_ok 224 hsa.align hsa.limit hsa.rootRead hsa.recipRead fun b hb hz hbar => ?_
  refine scaleRun_ok _ (va.roots hb) ?_ ?_ ?_ fun t ht vt => ?_
  · rw [hz]; exact hsa.root
  · rw [hbar]; exact hsa.recip
  · rw [hb.get .v31 (by decide),ha.get .v31 (by decide)]; exact hq
  · refine k t (((ha.trans hb).trans ht).mono ?_) ?_
    · intro r hr
      simp only [List.mem_append] at hr
      rcases hr with (hr | hr) | hr
      · exact hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ hr
    · simpa only [scaleRunValues_all,stageRunValues_all,Inverse.rawFinalValues] using vt

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
