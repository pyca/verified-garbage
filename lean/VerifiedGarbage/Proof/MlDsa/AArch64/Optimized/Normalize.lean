import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt

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
