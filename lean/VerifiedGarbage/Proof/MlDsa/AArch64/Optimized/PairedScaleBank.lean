import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStageRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseScale

/-! ## From `PairedScale.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def scalePairs (j : Fin 4) : List (VReg × VReg) := [(vr j.val,.v24),(vr (8+j.val),.v25)]
def scaleStep (j : Fin 4) : List Instr :=
  (scalePairs j).map (fun p => Instr.vop (.sqdmulh p.2 p.1 .v29)) ++
  ((scalePairs j).map Prod.fst).map (fun d => Instr.vop (.mul d d .v28)) ++
  (scalePairs j).map (fun p => Instr.vop (.mls p.1 p.2 .v31))

theorem scale_shape (j : Fin 4) :
    ((scalePairs j).map Prod.fst).Nodup ∧ ((scalePairs j).map Prod.snd).Nodup ∧
    (∀p∈scalePairs j,p.1∉(scalePairs j).map Prod.snd) ∧
    (∀p∈scalePairs j,p.2∉(scalePairs j).map Prod.fst) ∧
    .v28∉(scalePairs j).map Prod.fst ∧ .v28∉(scalePairs j).map Prod.snd ∧
    .v29∉(scalePairs j).map Prod.snd ∧ .v31∉(scalePairs j).map Prod.fst ∧
    .v31∉(scalePairs j).map Prod.snd := by
  revert j
  decide

theorem scaleStep_ok (j : Fin 4) {s : State} {rest : List Instr} {Q : State → Prop}
    (hz : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 16382)
    (hb : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal 16382))
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg ((scalePairs j).map Prod.snd++(scalePairs j).map Prod.fst) s t →
      (∀p∈scalePairs j,∀e<4,vword (t.v p.1) e=fastMulWord (vword (s.v p.1) e) 16382) →
      WP isa (.block rest) t Q) :
    WP isa (.block (scaleStep j++rest)) s Q := by
  obtain ⟨hd,ht,hdt,htd,hzd,hzt,hbt,hqd,hqt⟩ := scale_shape j
  exact multiply_batch_ok (scalePairs j) .v28 .v29 .v31 hd ht hdt htd hzd hzt hbt hqd hqt
    (z:=fun _ => 16382) (by intro e he; decide) hz hb hq k

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedScaleBank.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def scaleClobs (j : Fin 4) : List VReg := (scalePairs j).map Prod.snd++(scalePairs j).map Prod.fst

theorem scale_geometry (j : Fin 4) (p : Fin 2) (a : Fin 8) :
    (((bankRegs p)[j.val],if p.val=0 then .v24 else .v25)∈scalePairs j) ∧
    (a.val≠j.val → (bankRegs p)[a.val]∉scaleClobs j) := by
  revert j p a
  decide

def scaleOne (v : Vector (BitVec 128) 8) (j : Fin 4) : Vector (BitVec 128) 8 :=
  v.set j.val (fastVector v[j.val] (fun _ => 16382))

theorem scaleBank_ok (j : Fin 4) {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Values} (hv : Banks s v)
    (hz : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 16382)
    (hb : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal 16382))
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg (scaleClobs j) s t → Banks t (fun p => scaleOne (v p) j) →
      WP isa (.block rest) t Q) :
    WP isa (.block (scaleStep j++rest)) s Q := by
  refine scaleStep_ok j hz hb hq fun t ht hh => k t ht ?_
  intro p a
  have hm := (scale_geometry j p a).1
  simp only [scaleOne,Vector.getElem_set]
  by_cases ha : j.val=a.val
  · simp only [ha,ite_true]
    have he : (⟨j.val,by omega⟩:Fin 8)=a := Fin.ext ha
    apply vec_ext
    intro e he'
    have hreg := congrArg (fun a:Fin 8 => (bankRegs p)[a.val]) he
    have hval := congrArg (fun a:Fin 8 => (v p)[a.val]) he
    rw [← hreg,← hval]
    rw [hh _ hm e he',hv p ⟨j.val,by omega⟩]
    rw [fastVector_word _ _ he']
  · simp only [ha,ite_false]
    rw [ht.get _ ((scale_geometry j p a).2 (Ne.symm ha)),hv p a]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
