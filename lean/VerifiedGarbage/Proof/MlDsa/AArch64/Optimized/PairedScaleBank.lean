import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedScale

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
