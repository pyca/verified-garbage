import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailRun

/-! ## From `Normalize.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def positiveVector (v : BitVec 128) : BitVec 128 :=
  ofVWords (positiveWord (vword v 0)) (positiveWord (vword v 1))
    (positiveWord (vword v 2)) (positiveWord (vword v 3))

theorem positiveVector_word (v : BitVec 128) {e : Nat} (he : e < 4) :
    vword (positiveVector v) e = positiveWord (vword v e) := by
  rw [positiveVector, VG.AArch64.vword_ofVWords _ _ _ _ he]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- Normalizing the complete bank neither assumes nor establishes canonical
representatives: the exact outputs are positive and below 3q. -/
theorem positive_many_ok (regs : List VReg) (hd : regs.Nodup)
    (ha : ∀ d ∈ regs, d ≠ .v4 ∧ d ≠ .v16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀ e < 4, vword (s.v .v16) e = 8380417#32)
    (k : ∀ t, VChg (.v4::regs) s t →
      (∀ d ∈ regs, t.v d = positiveVector (s.v d)) → WP isa (.block rest) t Q) :
    WP isa (.block (regs.flatMap canon ++ rest)) s Q := by
  induction regs generalizing s with
  | nil => exact k s (VChg.refl _ _) (by simp)
  | cons d regs ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine positive_ok (ha d (by simp)).1 (ha d (by simp)).2 (by decide) hq
      fun s₁ hc₁ hv₁ => ?_
    have hdv : s₁.v d = positiveVector (s.v d) := by
      apply VG.AArch64.vec_ext
      intro e he
      rw [hv₁ e he,positiveVector_word _ he]
    have hq₁ : ∀ e < 4, vword (s₁.v .v16) e = 8380417#32 := by
      intro e he
      rw [hc₁.get .v16 (by simp [(ha d (by simp)).2.symm])]
      exact hq e he
    refine ih (List.nodup_cons.mp hd).2 (fun d hp => ha d (List.mem_cons_of_mem _ hp)) hq₁
      fun s₂ hc₂ hv₂ => k s₂ (VChg.mono (hc₁.trans hc₂) ?_) ?_
    · intro v hv
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hv ⊢
      grind only
    · intro a hm
      rcases List.mem_cons.mp hm with he | hm
      · subst a
        rw [hc₂.get d (by simp [(ha d (by simp)).1, (List.nodup_cons.mp hd).1]),hdv]
      · rw [hv₂ a hm,hc₁.get a ?_]
        have had : a ≠ d := by
          intro he
          exact (List.nodup_cons.mp hd).1 (he ▸ hm)
        simp [had,(ha a (List.mem_cons_of_mem _ hm)).1]

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `NormalizeBank.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem normalizeBank_ok (regs : Vector VReg 8) (hd : regs.toList.Nodup)
    (ha : ∀ d ∈ regs.toList, d ≠ .v4 ∧ d ≠ .v16)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    (hb : Bank s regs values) (hq : ∀ e < 4, vword (s.v .v16) e = 8380417#32)
    (k : ∀ t, VChg (.v4::regs.toList) s t →
      Bank t regs (values.map positiveVector) → WP isa (.block rest) t Q) :
    WP isa (.block (regs.toList.flatMap canon ++ rest)) s Q := by
  refine positive_many_ok regs.toList hd ha hq fun t hc hv => k t hc ?_
  intro i
  have hi : i.val < regs.toList.length := by simp
  have hm : regs[i.val] ∈ regs.toList := by
    simpa only [Vector.getElem_toList] using List.getElem_mem hi
  rw [hv _ hm,hb i,Vector.getElem_map]

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `FiveCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def fiveRegs : List VReg := outerRegs ++ tailRegs

def fiveCoreCode : List Instr := (renThree false).code ++ tailCode (renThree false) tailSteps ++
  (renThree false).data.toList.flatMap canon

def fiveValues (v : Vector (BitVec 128) 8) (zi zt : Nat → Nat → Nat → Int) : Vector (BitVec 128) 8 :=
  (tailValues (innerValues v zi outerSteps) zt tailSteps).map positiveVector

/-- The exact five fused inner layers, followed by positive normalization. -/
theorem fiveCore_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} {zi zt : Nat → Nat → Nat → Int}
    (hb : Bank s ({} : Ren).data v) (hi : InnerRoots s zi) (ht : TailRoots s zt)
    (k : ∀ t, VChg fiveRegs s t →
      Bank t (renThree false).data (fiveValues v zi zt) → WP isa (.block rest) t Q) :
    WP isa (.block (fiveCoreCode ++ rest)) s Q := by
  simp only [fiveCoreCode,List.append_assoc]
  refine innerThree_ok hb hi fun s₁ hc₁ _ hb₁ => ?_
  refine tailRun_ok (renThree false) tailSteps tailSteps_valid (renThree_good false)
    hb₁ (ht.keep_of hc₁ (by decide)) fun s₂ hc₂ ht₂ hb₂ => ?_
  have hd : (renThree false).data.toList.Nodup := by rw [renThree_data]; decide
  have ha : ∀ d ∈ (renThree false).data.toList, d ≠ VReg.v4 ∧ d ≠ VReg.v16 := by
    rw [renThree_data]
    decide
  refine normalizeBank_ok (renThree false).data hd ha hb₂ ht₂.q fun s₃ hc₃ hb₃ => k s₃ ?_ hb₃
  have hs : (.v4::(renThree false).data.toList) ⊆ tailRegs := by
    rw [renThree_data]
    decide
  refine VChg.mono ((hc₁.trans hc₂).trans (hc₃.mono hs)) ?_
  intro v hv
  simp only [fiveRegs,List.mem_append] at hv ⊢
  exact hv.elim id Or.inr

end VG.Proof.MlDsa.AArch64.Optimized

end
