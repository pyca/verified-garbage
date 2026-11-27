module

import VerifiedGarbage.Proof.Framework.Omega

/-!
# Ranges that are apart

That the ranges of `n` bytes at the offsets of a list are pairwise apart (or the
same), as the kernel evaluates it: one walk of the list, with the bytes of the
offsets met so far as the bits of a number, where the decision over all pairs
compares each of hundreds of offsets with every other (`apart_of`).
-/

@[expose] public section

namespace VG

/-- `apart`, of the offsets `l`, with those before them the bits of `s`, and their bytes those of `b`. -/
noncomputable def apartFrom (n : Nat) (l : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun x _ ih s b => Bool.rec
      (Bool.rec false (ih (Nat.lor s (Nat.shiftLeft 1 x)) (Nat.lor b (Nat.shiftLeft (Nat.pred (Nat.pow 2 n)) x)))
        (Nat.beq (Nat.land (Nat.shiftRight b x) (Nat.pred (Nat.pow 2 n))) 0))
      (ih s b) (Nat.beq (Nat.land (Nat.shiftRight s x) 1) 1)) l

/-- The ranges of `n` bytes at the offsets of `l` are pairwise apart, or the same. -/
noncomputable def apart (n : Nat) (l : List Nat) : Bool := apartFrom n l 0 0

theorem apartFrom_ok {n : Nat} : ∀ (l : List Nat) (seen : List Nat) (s b : Nat),
    (∀ x, s.testBit x = true ↔ x ∈ seen) → (∀ x ∈ seen, ∀ i < n, b.testBit (x + i) = true) →
    (∀ x ∈ seen, ∀ y ∈ seen, x ≠ y → x + n ≤ y ∨ y + n ≤ x) → apartFrom n l s b = true →
    ∀ x ∈ seen ++ l, ∀ y ∈ seen ++ l, x ≠ y → x + n ≤ y ∨ y + n ≤ x
  | [], seen, _, _, _, _, hp, _ => by rw [List.append_nil]; exact hp
  | x :: l, seen, s, b, hs, hb, hp, h => by
    have hbit : Nat.beq (Nat.land (Nat.shiftRight s x) 1) 1 = s.testBit x := by
      rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
      show Nat.beq (s >>> x &&& 1) 1 = _
      rw [Nat.and_one_is_mod]
      by_cases hm : s >>> x % 2 = 1
      · rw [hm]; rfl
      · rw [decide_eq_false hm]; exact Bool.eq_false_iff.mpr fun e => hm (Nat.beq_eq.mp e)
    have h : Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (apartFrom n l (Nat.lor s (Nat.shiftLeft 1 x)) (Nat.lor b (Nat.shiftLeft (Nat.pred (Nat.pow 2 n)) x)))
        (Nat.beq (Nat.land (Nat.shiftRight b x) (Nat.pred (Nat.pow 2 n))) 0))
      (apartFrom n l s b) (Nat.beq (Nat.land (Nat.shiftRight s x) 1) 1) = true := h
    rw [hbit] at h
    cases hx : s.testBit x with
    | true =>
      rw [hx] at h
      have := apartFrom_ok l seen s b hs hb hp h
      have hm : ∀ z, z ∈ seen ++ x :: l → z ∈ seen ++ l := fun z hz => by
        rcases List.mem_append.mp hz with hz | hz
        · exact List.mem_append_left _ hz
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact List.mem_append_left _ ((hs z).mp hx)
          · exact List.mem_append_right _ hz
      exact fun u hu v hv => this u (hm u hu) v (hm v hv)
    | false =>
      rw [hx] at h
      cases hz : Nat.beq (Nat.land (Nat.shiftRight b x) (Nat.pred (Nat.pow 2 n))) 0 with
      | false => rw [hz] at h; cases h
      | true =>
        rw [hz] at h
        have hz : (b >>> x) &&& (2 ^ n - 1) = 0 := Nat.beq_eq.mp hz
        have free (i : Nat) (hi : i < n) : b.testBit (x + i) = false := by
          have := congrArg (·.testBit i) hz
          simpa only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, hi, decide_true,
            Bool.and_true, Nat.zero_testBit] using this
        have key (y : Nat) (hy : y ∈ seen) : x + n ≤ y ∨ y + n ≤ x := by
          by_cases c1 : x + n ≤ y
          · exact .inl c1
          by_cases c2 : y + n ≤ x
          · exact .inr c2
          by_cases c : x ≤ y
          · have h1 := free (y - x) (by omega_using [c, c1])
            rw [show x + (y - x) = y + 0 by omega_using [c], hb y hy 0 (by omega_using [c1, c2])] at h1
            cases h1
          · have h1 := free 0 (by omega_using [c1, c2])
            have h2 := hb y hy (x - y) (by omega_using [c, c2])
            rw [show y + (x - y) = x + 0 by omega_using [c], h1] at h2
            cases h2
        have e : (seen ++ [x]) ++ l = seen ++ x :: l := by rw [List.append_assoc]; rfl
        rw [← e]
        refine apartFrom_ok l (seen ++ [x]) _ _ (fun z => ?_) (fun z hz i hi => ?_) (fun u hu v hv hne => ?_) h
        · show (s ||| 1 <<< x).testBit z = true ↔ _
          rw [Nat.testBit_or, Bool.or_eq_true, hs, List.mem_append, List.mem_singleton, Nat.one_shiftLeft,
            Nat.testBit_two_pow, decide_eq_true_eq]
          exact or_congr_right eq_comm
        · show (b ||| (2 ^ n - 1) <<< x).testBit (z + i) = true
          rw [Nat.testBit_or, Bool.or_eq_true]
          rcases List.mem_append.mp hz with hz | hz
          · exact .inl (hb z hz i hi)
          · right
            rw [List.mem_singleton.mp hz, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Bool.and_eq_true]
            exact ⟨decide_eq_true (Nat.le_add_right x i), decide_eq_true (by omega_using [hi])⟩
        · rcases List.mem_append.mp hu with hu | hu <;> rcases List.mem_append.mp hv with hv | hv
          · exact hp u hu v hv hne
          · rw [List.mem_singleton.mp hv]; exact (key u hu).symm
          · rw [List.mem_singleton.mp hu]; exact key v hv
          · exact absurd ((List.mem_singleton.mp hu).trans (List.mem_singleton.mp hv).symm) hne

theorem apart_of {n : Nat} {l : List Nat} (h : apart n l = true) :
    ∀ x ∈ l, ∀ y ∈ l, x ≠ y → x + n ≤ y ∨ y + n ≤ x :=
  apartFrom_ok l [] 0 0 (fun x => by simp only [Nat.zero_testBit, Bool.false_eq_true, List.not_mem_nil])
    (fun _ hx => absurd hx List.not_mem_nil) (fun _ hx => absurd hx List.not_mem_nil) h

end VG
