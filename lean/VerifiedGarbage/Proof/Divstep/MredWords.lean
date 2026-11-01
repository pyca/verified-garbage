module

public import VerifiedGarbage.Proof.Divstep.SignedWords
public import VerifiedGarbage.Proof.Divstep.Alg

/-!
# One word of Montgomery reduction on signed multiword numbers

`mredRaw p m t` (`Proof/Divstep/Alg.lean`) as code computes it on `t`, a
signed number of `L` words: sign-extended to `L + 1` words, `k p` added for
`k = t₀ m mod 2^64` modulo `2^(64 (L + 1))`, and the words above the lowest
kept (`mredSext_words`). Signed numbers modulo `2^(64 L)` (`sgn_emod`,
`sgn_of_emod`).
-/

@[expose] public section

namespace VG.Proof.Divstep

theorem pow64_cast (L : Nat) : ((2 ^ (64 * L) : Nat) : Int) = 2 ^ (64 * L) := by push_cast; rfl

/-- `2^(64 L)` and `2^(64 L - 1)` through `H`. -/
theorem pow_H {L : Nat} (hL : 1 ≤ L) : ∃ H : Nat, 2 ^ 63 ≤ H ∧ 2 ^ (64 * L - 1) = H ∧ 2 ^ (64 * L) = 2 * H ∧
    (2 : Int) ^ (64 * L - 1) = H ∧ (2 : Int) ^ (64 * L) = 2 * H := by
  obtain ⟨e, h63⟩ := pow_half hL
  refine ⟨_, h63, rfl, e, by push_cast; rfl, ?_⟩
  rw [← pow64_cast, e]; push_cast; rfl

/-- A signed number is its words modulo `2^(64 L)`. -/
theorem sgn_emod {L x : Nat} (hL : 1 ≤ L) (hx : x < 2 ^ (64 * L)) : sgn L x % 2 ^ (64 * L) = x := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  unfold sgn
  simp only [e1, e4]; rw [e2] at hx
  split
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · rw [show (x : Int) - 2 * H = x + (-1) * (2 * H) by omega, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- The signed number of `L` words congruent to `y`, if `y` fits. -/
theorem sgn_of_emod {L x : Nat} {y : Int} (hL : 1 ≤ L)
    (hy₀ : -2 ^ (64 * L - 1) ≤ y) (hy₁ : y < 2 ^ (64 * L - 1)) (h : (x : Int) = y % 2 ^ (64 * L)) :
    sgn L x = y := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  unfold sgn
  simp only [e1, e4]; rw [e3] at hy₀ hy₁; rw [e4] at h
  by_cases hy : 0 ≤ y
  · rw [Int.emod_eq_of_lt hy (by omega)] at h
    rw [ite_eq_left (by omega : x < H)]; exact h
  · rw [show y = (y + 2 * H) + (-1) * (2 * H) by omega, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (by omega) (by omega)] at h
    rw [ite_eq_right (by omega : ¬ x < H)]; omega

/-- Sign extension by a word: the top word's sign mask. -/
theorem sext_emod {L S : Nat} (hL : 1 ≤ L) :
    ((S + 2 ^ (64 * L) * (if S < 2 ^ (64 * L - 1) then 0 else 2 ^ 64 - 1) : Nat) : Int) =
      sgn L S + (if S < 2 ^ (64 * L - 1) then 0 else 2 ^ (64 * (L + 1))) := by
  obtain ⟨e, h63⟩ := pow_half hL
  have e2 : (2 : Int) ^ (64 * (L + 1)) = 2 ^ (64 * L) * 2 ^ 64 := by rw [Nat.mul_succ, Int.pow_add]
  unfold sgn
  rw [e2]
  split
  · simp
  · push_cast; grind

/-- One word of Montgomery reduction of the signed `L`-word `S` as the code
computes it: `W₁` the sign extension, `k = S₀ m mod 2^64`, `W₂ = W₁ + k p`
modulo `2^(64 (L + 1))`, and `O` its words above the lowest. -/
theorem mredSext_words {L S W₂ O : Nat} {k p m : Int} (hL : 1 ≤ L)
    (hm : (p * m + 1) % 2 ^ 64 = 0) (hk : k = (S % 2 ^ 64 : Nat) * m % 2 ^ 64)
    (hW₂ : (W₂ : Int) = ((S + 2 ^ (64 * L) * (if S < 2 ^ (64 * L - 1) then 0 else 2 ^ 64 - 1) : Nat) + k * p) %
      2 ^ (64 * (L + 1)))
    (hO : W₂ = W₂ % 2 ^ 64 + 2 ^ 64 * O) :
    (O : Int) = mredRaw p m (sgn L S) % 2 ^ (64 * L) := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  have eQP : (2 : Int) ^ (64 * (L + 1)) = 2 ^ 64 * 2 ^ (64 * L) := by
    rw [Nat.mul_succ, Int.pow_add, Int.mul_comm]
  have eP : (2 : Int) ^ (64 * L) = 2 ^ (64 * L - 64) * 2 ^ 64 := by rw [← Int.pow_add]; congr 1; omega
  set tv := sgn L S with htv
  -- `S ≡ tv` modulo `2^64`.
  have hS64 : ((S % 2 ^ 64 : Nat) : Int) % 2 ^ 64 = tv % 2 ^ 64 := by
    rw [htv, Int.natCast_mod, show ((2 ^ 64 : Nat) : Int) = 2 ^ 64 by rfl, Int.emod_emod]; unfold sgn
    split
    · rfl
    · rw [eP, show (S : Int) - 2 ^ (64 * L - 64) * 2 ^ 64 = S + (-2 ^ (64 * L - 64)) * 2 ^ 64 by grind,
        Int.add_mul_emod_self_right]
  have hk' : k = tv * m % 2 ^ 64 := by
    rw [hk, Int.mul_emod, hS64, ← Int.mul_emod]
  -- `2^64` divides `tv + k p`.
  have hdvd : (2 : Int) ^ 64 ∣ tv + k * p := by
    have h1 : (2 : Int) ^ 64 ∣ tv * (p * m + 1) := Int.dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero hm)
    have h2 : (2 : Int) ^ 64 ∣ tv * m - k := by
      rw [hk']; exact Int.dvd_self_sub_emod
    have := Int.dvd_sub h1 (Int.dvd_mul_of_dvd_left (c := p) h2)
    rw [show tv * (p * m + 1) - (tv * m - k) * p = tv + k * p by grind] at this
    exact this
  obtain ⟨R, hR⟩ := hdvd
  have hW : (W₂ : Int) = 2 ^ 64 * (R % 2 ^ (64 * L)) := by
    rw [hW₂, sext_emod hL]
    rw [show sgn L S + (if S < 2 ^ (64 * L - 1) then 0 else (2 : Int) ^ (64 * (L + 1))) + k * p =
      (tv + k * p) + (if S < 2 ^ (64 * L - 1) then 0 else 1) * 2 ^ (64 * (L + 1)) by split <;> grind,
      Int.add_mul_emod_self_right, hR, eQP, Int.mul_emod_mul_of_pos _ _ (by decide)]
  have hmr : mredRaw p m tv = R := by
    unfold mredRaw; rw [← hk', hR, Int.mul_ediv_cancel_left _ (by decide)]
  rw [hmr]
  have h0 : (W₂ % 2 ^ 64 : Nat) = 0 := by
    have : (W₂ : Int) % 2 ^ 64 = 0 := by rw [hW]; exact Int.mul_emod_right _ _
    omega
  rw [h0, Nat.zero_add] at hO
  have : (W₂ : Int) = 2 ^ 64 * O := by rw [hO]; push_cast; rfl
  rw [hW] at this
  exact (Int.eq_of_mul_eq_mul_left (by decide) this).symm

/-- A linear combination's words, from unsigned words and a carry, as a
signed number, if it fits. -/
theorem lin_sgn {L W F G : Nat} {u v c : Int} (hL : 1 ≤ L) (hW : W < 2 ^ (64 * L)) (hF : F < 2 ^ (64 * L))
    (hG : G < 2 ^ (64 * L)) (h : (W : Int) + 2 ^ (64 * L) * c = u * F + v * G)
    (r₀ : -2 ^ (64 * L - 1) ≤ u * sgn L F + v * sgn L G) (r₁ : u * sgn L F + v * sgn L G < 2 ^ (64 * L - 1)) :
    sgn L W = u * sgn L F + v * sgn L G := by
  refine sgn_of_emod hL r₀ r₁ ?_
  have eF := Int.emod_add_mul_ediv (sgn L F) (2 ^ (64 * L))
  have eG := Int.emod_add_mul_ediv (sgn L G) (2 ^ (64 * L))
  rw [sgn_emod hL hF] at eF; rw [sgn_emod hL hG] at eG
  have hP : (0 : Int) < 2 ^ (64 * L) := Int.pow_pos (by decide)
  rw [show u * sgn L F + v * sgn L G = W + (2 ^ (64 * L)) * (c + u * (sgn L F / 2 ^ (64 * L)) +
    v * (sgn L G / 2 ^ (64 * L))) by rw [← eF, ← eG] at *; grind, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast hW)]

/-- A signed number's low word. -/
theorem sgn_mod64 {L F : Nat} (hL : 1 ≤ L) (hF : F < 2 ^ (64 * L)) : sgn L F % 2 ^ 64 = ((F % 2 ^ 64 : Nat) : Int) := by
  have e := Int.emod_add_mul_ediv (sgn L F) (2 ^ (64 * L))
  rw [sgn_emod hL hF] at e
  have hd : (2 : Int) ^ 64 ∣ 2 ^ (64 * L) := ⟨2 ^ (64 * L - 64), by rw [← Int.pow_add]; congr 1; omega⟩
  rw [← e, Int.add_emod, Int.emod_eq_zero_of_dvd (Int.dvd_mul_of_dvd_left hd), Int.add_zero, Int.emod_emod]
  rfl

/-- A word's signed value is a small integer's. -/
theorem toInt_ofInt64 {u : Int} (h0 : -2 ^ 63 ≤ u) (h1 : u < 2 ^ 63) : (BitVec.ofInt 64 u).toInt = u := by
  rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)


/-! ## Negating and correcting signed numbers -/

/-- The sign of a number of `n + 1` words is its top word's top bit. -/
theorem sgn_neg_iff {n W s : Nat} (hW : W < 2 ^ (64 * n)) (hs : s < 2 ^ 64) :
    sgn (n + 1) (W + 2 ^ (64 * n) * s) < 0 ↔ 2 ^ 63 ≤ s := by
  have t := top_sign hW hs
  unfold sgn
  have hR : W + 2 ^ (64 * n) * s < 2 ^ (64 * (n + 1)) := by
    have : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
      rw [← Nat.pow_add, show 64 * n + 64 = 64 * (n + 1) by omega]
    have := Nat.mul_le_mul_left (2 ^ (64 * n)) (show s + 1 ≤ 2 ^ 64 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  split
  · rename_i h; exact ⟨fun h' => by omega, fun h' => absurd (t.mp h) (by omega)⟩
  · rename_i h
    refine ⟨fun _ => Nat.le_of_not_lt fun h' => h (t.mpr h'), fun _ => ?_⟩
    have : ((W + 2 ^ (64 * n) * s : Nat) : Int) < 2 ^ (64 * (n + 1)) := by exact_mod_cast hR
    omega

/-- `([x] ^ mask) + neg`, `neg` the mask's bit: `[x]` negated if `neg`. -/
theorem sgn_cneg {L X Y c : Nat} {neg : Bool} (hL : 1 ≤ L) (hX : X < 2 ^ (64 * L)) (hY : Y < 2 ^ (64 * L))
    (hr : -2 ^ (64 * L - 1) < sgn L X)
    (h : Y + 2 ^ (64 * L) * c = (if neg then 2 ^ (64 * L) - 1 - X else X) + neg.toNat) :
    sgn L Y = if neg then -sgn L X else sgn L X := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  rw [e3] at hr
  unfold sgn at hr ⊢
  simp only [e1, e4] at hr ⊢
  rw [e2] at hX hY h
  cases neg
  · simp only [Bool.false_eq_true, ite_false, Bool.toNat_false, Nat.add_zero] at h ⊢
    have hc : c = 0 := by
      rcases Nat.eq_zero_or_pos c with hc | hc
      · exact hc
      · have := Nat.mul_le_mul_left (2 * H) hc; omega
    subst hc
    rw [Nat.mul_zero, Nat.add_zero] at h
    subst h
    rfl
  · simp only [ite_true, Bool.toNat_true] at h ⊢
    by_cases hx : X < H
    · rw [ite_eq_left hx]
      by_cases x0 : X = 0
      · subst x0
        have hc : c = 1 := by
          rcases Nat.lt_or_ge c 2 with hc | hc
          · rcases Nat.lt_or_ge c 1 with hc' | hc'
            · have : c = 0 := by omega
              subst this; omega
            · omega
          · have := Nat.mul_le_mul_left (2 * H) hc; omega
        subst hc
        have : Y = 0 := by omega
        subst this
        rw [ite_eq_left (show (0 : Nat) < H by omega)]; simp
      · have hc : c = 0 := by
          rcases Nat.eq_zero_or_pos c with hc | hc
          · exact hc
          · have := Nat.mul_le_mul_left (2 * H) hc; omega
        subst hc
        rw [ite_eq_right (by omega : ¬ Y < H)]
        push_cast
        omega
    · rw [ite_eq_right hx] at hr ⊢
      have hc : c = 0 := by
        rcases Nat.eq_zero_or_pos c with hc | hc
        · exact hc
        · have := Nat.mul_le_mul_left (2 * H) hc; omega
      subst hc
      rw [ite_eq_left (by omega : Y < H)]
      push_cast at hr ⊢
      omega

/-- `[x] += p` modulo `2^(64 L)` if `[x]` is negative. -/
theorem sgn_addIfNeg {L X Y : Nat} {p : Int} (hL : 1 ≤ L) (hX : X < 2 ^ (64 * L))
    (hY : (Y : Int) = (X + if sgn L X < 0 then p else 0) % 2 ^ (64 * L))
    (r₀ : -2 ^ (64 * L - 1) ≤ sgn L X + if sgn L X < 0 then p else 0)
    (r₁ : sgn L X + (if sgn L X < 0 then p else 0) < 2 ^ (64 * L - 1)) :
    sgn L Y = sgn L X + if sgn L X < 0 then p else 0 := by
  refine sgn_of_emod hL r₀ r₁ ?_
  rw [hY, Int.add_emod, ← sgn_emod hL hX, Int.emod_emod, ← Int.add_emod]

end VG.Proof.Divstep
