import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

/-- The per-lane accumulator records whether any processed group failed. -/
def flagBad (bad : Nat → Nat → Bool) : Nat → Nat → Bool
  | 0,_ => false
  | j+1,e => flagBad bad j e || bad j e

theorem maskWord_or (a b : Bool) : maskWord a ||| maskWord b=maskWord (a||b) := by
  cases a <;> cases b <;> rfl

theorem flagBad_false (bad : Nat → Nat → Bool) (j e : Nat) :
    flagBad bad j e=false ↔ ∀i<j,bad i e=false := by
  induction j with
  | zero => simp [flagBad]
  | succ j ih =>
    simp only [flagBad,Bool.or_eq_false_iff,ih]
    constructor
    · rintro ⟨h,hj⟩ i hi
      by_cases he : i=j
      · simpa only [he] using hj
      · exact h i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega),h j (by omega)⟩

theorem finishValue_flags {v : BitVec 128} {bad : Nat → Nat → Bool} {j : Nat}
    (h : ∀e<4,vword v e=maskWord (flagBad bad j e)) :
    finishValue v=1 ↔ (∀i<j,∀e<4,bad i e=false) := by
  have hv : v=ofVWords (maskWord (flagBad bad j 0)) (maskWord (flagBad bad j 1))
      (maskWord (flagBad bad j 2)) (maskWord (flagBad bad j 3)) := by
    apply vec_ext
    intro e he
    rw [h e he,vword_ofVWords _ _ _ _ he]
    rcases (show e=0∨e=1∨e=2∨e=3 by omega) with rfl|rfl|rfl|rfl <;> rfl
  rw [hv,finishValue_masks]
  have he : (flagBad bad j 0 || flagBad bad j 1 || flagBad bad j 2 || flagBad bad j 3)=false ↔
      ∀i<j,∀e<4,bad i e=false := by
    simp only [Bool.or_eq_false_iff,flagBad_false]
    constructor
    · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩ i hi e he
      rcases (show e=0∨e=1∨e=2∨e=3 by omega) with rfl|rfl|rfl|rfl
      · exact h0 i hi
      · exact h1 i hi
      · exact h2 i hi
      · exact h3 i hi
    · intro h
      exact ⟨⟨⟨fun i hi=>h i hi 0 (by decide),fun i hi=>h i hi 1 (by decide)⟩,
        fun i hi=>h i hi 2 (by decide)⟩,fun i hi=>h i hi 3 (by decide)⟩
  rw [← he]
  cases hbad : (flagBad bad j 0 || flagBad bad j 1 || flagBad bad j 2 || flagBad bad j 3) <;> simp

theorem finishValue_flags_range {v : BitVec 128} {bad : Nat → Nat → Bool} {j : Nat}
    (h : ∀e<4,vword v e=maskWord (flagBad bad j e)) :
    finishValue v=0 ∨ finishValue v=1 := by
  have hv : v=ofVWords (maskWord (flagBad bad j 0)) (maskWord (flagBad bad j 1))
      (maskWord (flagBad bad j 2)) (maskWord (flagBad bad j 3)) := by
    apply vec_ext
    intro e he
    rw [h e he,vword_ofVWords _ _ _ _ he]
    rcases (show e=0∨e=1∨e=2∨e=3 by omega) with rfl|rfl|rfl|rfl <;> rfl
  rw [hv,finishValue_masks]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
