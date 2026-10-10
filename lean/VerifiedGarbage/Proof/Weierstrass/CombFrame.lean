import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.Unch

/-!
# The fixed-base comb: what its steps leave unchanged

Facts about the comb's slots that every target's proof of an iteration needs
(the entry writing `E`, its negation and the temporary area; the addition
writing `D`; the selections writing `D` and `A`), proven once from the layout
(`CombLay`) rather than in each target's proof: which slots each step leaves
unchanged, the apartness the selections need, and that each step writes
within what the comb writes (`combW`).
-/

namespace VG.Proof.Weierstrass

open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Proof.Mont

variable {K : CombCfg} {size : Nat}

/-- What the entry writes: `E`, its negation and the temporary area. -/
def combEntryW (K : CombCfg) : List (Nat × Nat) :=
  [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]

/-- What the addition into `D` writes. -/
def combAddW (K : CombCfg) : List (Nat × Nat) :=
  (rcbW K.S K.D).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]

/-- What a selection into the point `o` writes. -/
def combSelW (K : CombCfg) (o : Pt) : List (Nat × Nat) :=
  [(o.x, 8 * K.M.n), (o.y, 8 * K.M.n), (o.z, 8 * K.M.n)]

theorem combEntryW_sub : ∀ w ∈ combEntryW K, w ∈ combW K := by
  intro w hw
  simp only [combEntryW, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  rcases hw with h | h | h | h | h <;> subst h <;> simp

theorem combAddW_sub : ∀ w ∈ combAddW K, w ∈ combW K := by
  intro w hw
  simp only [combAddW, combW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | h
  · exact Or.inl ⟨y, by simp only [combWs, List.mem_append]; exact Or.inr hy, rfl⟩
  · exact Or.inr h

theorem combSelW_D_sub : ∀ w ∈ combSelW K K.D, w ∈ combW K := by
  intro w hw
  simp only [combSelW, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [combW, combWs, rcbW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  rcases hw with h | h | h <;> subst h <;> simp

theorem combSelW_A_sub : ∀ w ∈ combSelW K K.A, w ∈ combW K := by
  intro w hw
  simp only [combSelW, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  rcases hw with h | h | h <;> subst h <;> simp

namespace CombLay

/-- `A` is unchanged by the entry. -/
theorem wordsVal_entry (hL : CombLay K size) (hsz : size ≤ 2 ^ 64) {base : Addr} {m m' : Mem}
    (h : Unch base (combEntryW K) m m') :
    ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  intro x hx
  have hxs : x ∈ combWs K := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> comb_mem
  refine h.wordsVal (fun w hw => ?_) (by have := hL.lay.le x (combWs_slots _ x hxs); omega)
  simp only [combEntryW, List.mem_cons, List.not_mem_nil, or_false] at hw hx
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · rcases hx with rfl | rfl | rfl <;> exact hL.apart₂ hxs (by comb_mem) (by nd_find hnd)
  · rcases hx with rfl | rfl | rfl <;> exact hL.apart₂ hxs (by comb_mem) (by nd_find hnd)
  · rcases hx with rfl | rfl | rfl <;> exact hL.apart₂ hxs (by comb_mem) (by nd_find hnd)
  · rcases hx with rfl | rfl | rfl <;> exact hL.apart₂ hxs (by comb_mem) (by nd_find hnd)
  · exact hL.lay.tmp x (combWs_slots _ x hxs)

/-- `A` and `E` are unchanged by the addition into `D`. -/
theorem wordsVal_add (hL : CombLay K size) (hsz : size ≤ 2 ^ 64) {base : Addr} {m m' : Mem}
    (h : Unch base (combAddW K) m m') :
    ∀ x ∈ [K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z],
      wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  intro x hx
  have hxs : x ∈ combWs K := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
  refine h.wordsVal (fun w hw => ?_) (by have := hL.lay.le x (combWs_slots _ x hxs); omega)
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    have hys : y ∈ combWs K := by simp only [combWs, List.mem_append]; exact Or.inr hy
    refine hL.apart₂ hxs hys ?_
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> nd_find hnd
  · simp only [List.mem_singleton] at hw; subst hw
    exact hL.lay.tmp x (combWs_slots _ x hxs)

/-- `A` is unchanged by a selection into `D`. -/
theorem wordsVal_selD (hL : CombLay K size) (hsz : size ≤ 2 ^ 64) {base : Addr} {m m' : Mem}
    (h : Unch base (combSelW K K.D) m m') :
    ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  intro x hx
  have hxs : x ∈ combWs K := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> comb_mem
  refine h.wordsVal (fun w hw => ?_) (by have := hL.lay.le x (combWs_slots _ x hxs); omega)
  simp only [combSelW, List.mem_cons, List.not_mem_nil, or_false] at hw hx
  rcases hw with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;>
    exact hL.apart₂ hxs (by comb_mem) (by nd_find hnd)

/-- The slots of `D` are apart. -/
theorem apart_D (hL : CombLay K size) :
    (K.D.x + 8 * K.M.n ≤ K.D.y ∨ K.D.y + 8 * K.M.n ≤ K.D.x) ∧
      (K.D.x + 8 * K.M.n ≤ K.D.z ∨ K.D.z + 8 * K.M.n ≤ K.D.x) ∧
      (K.D.y + 8 * K.M.n ≤ K.D.z ∨ K.D.z + 8 * K.M.n ≤ K.D.y) := by
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  exact ⟨hL.apart₂ (by comb_mem) (by comb_mem) (by nd_find hnd),
    hL.apart₂ (by comb_mem) (by comb_mem) (by nd_find hnd),
    hL.apart₂ (by comb_mem) (by comb_mem) (by nd_find hnd)⟩

/-- The slots of `A` are apart. -/
theorem apart_A (hL : CombLay K size) :
    (K.A.x + 8 * K.M.n ≤ K.A.y ∨ K.A.y + 8 * K.M.n ≤ K.A.x) ∧
      (K.A.x + 8 * K.M.n ≤ K.A.z ∨ K.A.z + 8 * K.M.n ≤ K.A.x) ∧
      (K.A.y + 8 * K.M.n ≤ K.A.z ∨ K.A.z + 8 * K.M.n ≤ K.A.y) := by
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  exact ⟨hL.apart₂ (by comb_mem) (by comb_mem) (by nd_find hnd),
    hL.apart₂ (by comb_mem) (by comb_mem) (by nd_find hnd),
    hL.apart₂ (by comb_mem) (by comb_mem) (by nd_find hnd)⟩

/-- `D` is apart from `E`. -/
theorem apart_DE (hL : CombLay K size) :
    ∀ x ∈ [K.D.x, K.D.y, K.D.z], ∀ y ∈ [K.E.x, K.E.y, K.E.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    exact hL.apart₂ (by comb_mem) (by comb_mem) (by nd_find hnd)

/-- `A` is apart from `D`. -/
theorem apart_AD (hL : CombLay K size) :
    ∀ x ∈ [K.A.x, K.A.y, K.A.z], ∀ y ∈ [K.D.x, K.D.y, K.D.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    exact hL.apart₂ (by comb_mem) (by comb_mem) (by nd_find hnd)

end CombLay

end VG.Proof.Weierstrass
