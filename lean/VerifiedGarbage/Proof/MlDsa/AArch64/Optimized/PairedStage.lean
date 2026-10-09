import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedGroupRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStage

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def stagePairs (i : Fin 7) : List (Fin 8 × Fin 8) :=
  match i.val with
  | 0 => [(0,1)]
  | 1 => [(2,3)]
  | 2 => [(4,5)]
  | 3 => [(6,7)]
  | 4 => [(0,2),(1,3)]
  | 5 => [(4,6),(5,7)]
  | _ => [(0,4),(1,5),(2,6),(3,7)]

theorem stagePairs_ne (i : Fin 7) : ∀p∈stagePairs i,p.1≠p.2 := by
  exact (show ∀i:Fin 7,∀p∈stagePairs i,p.1≠p.2 by decide) i

/-- The paired in-place scheduling has the same logical bank transition as
    the already verified register-renamed inverse groups. -/
theorem groupValues_stage (i : Fin 7) (v : Vector (BitVec 128) 8) (z : Nat → Int) :
    groupValues v z (stagePairs i)=Inverse.stageValues i.val v z := by
  have he (i : Fin 7) (j : Fin 8) :
      (groupValues v z (stagePairs i))[j.val]=(Inverse.stageValues i.val v z)[j.val] := by
    fin_cases i <;> fin_cases j <;>
      simp [stagePairs,groupValues,pairValues,Inverse.stageValues,Inverse.leftSide,
        Inverse.rightSide,Inverse.leftSource,Inverse.rightSource,Inverse.steps]
  exact Vector.ext fun j hj => he i ⟨j,hj⟩

open VG.Proof.MlKem.AArch64 (VChg)

theorem stage_ok (i : Fin 7) {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Values} {z : Nat → Int} (hv : Banks s v)
    (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg groupRegs s t → Banks t (fun p => Inverse.stageValues i.val (v p) z) →
      WP isa (.block rest) t Q) :
    WP isa (.block (groupCode (stagePairs i)++rest)) s Q := by
  refine groupRun_ok _ (stagePairs_ne i) hv hz hzw hbw hqw fun t ht hvt => k t ht ?_
  simpa only [groupValues_stage] using hvt

end VG.Proof.MlDsa.AArch64.Optimized.Paired
