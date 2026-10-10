import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedGroupRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStage
import VerifiedGarbage.Proof.MlDsa.Arith.Pairs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPackedRoot
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRun

/-! ## From `PairedStage.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Proof.MlDsa.Pairs

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

theorem groupValues_eq (v : Vector (BitVec 128) 8) (z : Nat → Int) (ps : List (Fin 8 × Fin 8)) :
    groupValues v z ps = pairsApply (fun a b => (VArr.s4.map2 (fun _ a b => a+b) a b,
      fastVector (VArr.s4.map2 (fun _ a b => a-b) a b) z)) v ps := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih => obtain ⟨i, j⟩ := p; exact ih _

/-- Which pair of stage `i` holds each entry: a finite fact. -/
theorem stagePairs_pairOf : ∀ i : Fin 7, ∀ k : Fin 8,
    (entries (stagePairs i)).Nodup ∧
    pairOf (stagePairs i) k = (if Inverse.leftSide i.val k.val ∨ Inverse.rightSide i.val k.val then
      some (Inverse.leftSource i.val k, Inverse.rightSource i.val k) else none) ∧
    (Inverse.leftSide i.val k.val → Inverse.leftSource i.val k = k) ∧
    (Inverse.rightSide i.val k.val → ¬Inverse.leftSide i.val k.val ∧ Inverse.leftSource i.val k ≠ k) := by
  decide +kernel

/-- The paired in-place scheduling has the same logical bank transition as
    the already verified register-renamed inverse groups. -/
theorem groupValues_stage (i : Fin 7) (v : Vector (BitVec 128) 8) (z : Nat → Int) :
    groupValues v z (stagePairs i)=Inverse.stageValues i.val v z := by
  refine Vector.ext fun k hk => ?_
  obtain ⟨hd, hp, hl, hr⟩ := stagePairs_pairOf i ⟨k, hk⟩
  rw [groupValues_eq, pairsApply_get _ _ hd ⟨k, hk⟩, hp]
  simp only [Inverse.stageValues, Vector.getElem_ofFn]
  by_cases h1 : Inverse.leftSide i.val k
  · simp only [h1, true_or, ite_true, hl h1]
  · by_cases h2 : Inverse.rightSide i.val k
    · simp only [h1, h2, or_true, ite_true, ite_false, (hr h2).2]
    · simp only [h1, h2, or_self, ite_false]

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

end

/-! ## From `PairedStageRun.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def stageRunRegs : List VReg := [.v28,.v29]++groupRegs

def stageRunCode (off : Fin 7 → Nat) (is : List (Fin 7)) : List Instr :=
  is.flatMap fun i => rootPair (off i)++groupCode (stagePairs i)

def stageRunValues (v : Vector (BitVec 128) 8) (z : Fin 7 → Nat → Int) :
    List (Fin 7) → Vector (BitVec 128) 8
  | [] => v
  | i::is => stageRunValues (Inverse.stageValues i.val v (z i)) z is

theorem stageRun_ok (is : List (Fin 7)) (off : Fin 7 → Nat) (z : Fin 7 → Nat → Int)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    (hv : Banks s v) (hr : ∀i,RootReady s (off i) (z i))
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg stageRunRegs s t → Banks t (fun p => stageRunValues (v p) z is) →
      WP isa (.block rest) t Q) :
    WP isa (.block (stageRunCode off is++rest)) s Q := by
  induction is generalizing s v with
  | nil => exact k s (VChg.refl _ _) hv
  | cons i is ih =>
    simp only [stageRunCode,List.flatMap_cons,List.append_assoc]
    refine rootLoads_ok (off i) (hr i).align (hr i).limit (hr i).rootRead (hr i).recipRead
      fun a ha hz hb => ?_
    refine stage_ok i (hv.roots ha) (hr i).bound ?_ ?_ ?_ fun b hbb vb => ?_
    · rw [hz]; exact (hr i).root
    · rw [hb]; exact (hr i).recip
    · rw [ha.get .v31 (by decide)]; exact hq
    have hc : VChg stageRunRegs s b := ha.trans hbb
    refine ih vb (fun j => (hr j).chg hc) ?_ fun t ht vt => ?_
    · rw [hc.get .v31 (by decide)]; exact hq
    · exact k t ((hc.trans ht).mono (by simp)) vt

theorem stageRunValues_all (v : Vector (BitVec 128) 8) (z : Nat → Nat → Int) :
    stageRunValues v (fun i => z i.val) (List.finRange 7)=Inverse.runValues z 0 7 v := by
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
