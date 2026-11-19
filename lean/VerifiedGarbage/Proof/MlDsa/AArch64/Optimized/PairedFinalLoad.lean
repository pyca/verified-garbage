module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStageRun
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawFinalSlice
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive

/-! ### `MlDsa.AArch64.Optimized.PairedFinalArithmetic`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedScaleBank`, which only this module used -/

section

/-! ## From `PairedScale.lean` -/

@[expose] public section

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
    have he : (⟨j.val,by omega_using []⟩:Fin 8)=a := Fin.ext ha
    apply vec_ext
    intro e he'
    have hreg := congrArg (fun a:Fin 8 => (bankRegs p)[a.val]) he
    have hval := congrArg (fun a:Fin 8 => (v p)[a.val]) he
    rw [← hreg,← hval]
    rw [hh _ hm e he',hv p ⟨j.val,by omega_using []⟩]
    rw [fastVector_word _ _ he']
  · simp only [ha,ite_false]
    rw [ht.get _ ((scale_geometry j p a).2 (Ne.symm ha)),hv p a]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end


/-! ## From `PairedScaleRun.lean` -/

@[expose] public section

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

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def readPair (m : Mem) (base : Addr) (stride : Nat) : Values := fun p => Vector.ofFn fun j =>
  m.read (base+BitVec.ofNat 64 (1024*p.val+stride*j.val)) 16

def finalLoads : List Instr := (pairStores 128).map (fun p => Instr.ldrq p.1 .x2 p.2)

theorem finalLoads_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      (s.gpr .x2+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (k : ∀t,VChg ((pairStores 128).map Prod.fst) s t →
      Banks t (readPair s.mem (s.gpr .x2) 128) → WP isa (.block rest) t Q) :
    WP isa (.block (finalLoads++rest)) s Q := by
  refine load_many_ok _ _ (by decide) (by decide) ?_ fun t ht hv => k t ht ?_
  · intro r hm
    obtain ⟨p,j,rfl⟩ := pairStores_mem.mp hm
    exact hr p j
  · intro p j
    simp only [readPair,Vector.getElem_ofFn]
    exact hv _ (pairStores_mem.mpr ⟨p,j,rfl⟩)

theorem finalLoadArithmetic_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      (s.gpr .x2+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (ht : ∀i:Fin 7,RootReady s (32*i.val) (Inverse.finalZ i.val))
    (hs : RootReady s 224 (fun _ => 16382))
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg stageRunRegs s t → Banks t (fun p =>
      Inverse.rawFinalValues (readPair s.mem (s.gpr .x2) 128 p)) → WP isa (.block rest) t Q) :
    WP isa (.block (finalLoads++finalArithmetic++rest)) s Q := by
  rw [List.append_assoc]
  refine finalLoads_ok hr fun a ha va => ?_
  refine finalArithmetic_ok va (fun i => (ht i).chg ha) (hs.chg ha) ?_ fun t hb vb => ?_
  · rw [ha.get .v31 (by decide)]; exact hq
  · exact k t ((ha.trans hb).mono (by decide)) vb

end VG.Proof.MlDsa.AArch64.Optimized.Paired
