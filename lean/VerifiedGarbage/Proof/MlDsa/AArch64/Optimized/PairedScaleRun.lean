import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedScaleBank

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
