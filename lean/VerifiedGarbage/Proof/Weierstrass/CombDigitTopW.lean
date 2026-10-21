module

public import VerifiedGarbage.Proof.Weierstrass.CombDigitW

/-! A comb may read only the actual bits of its final, shorter window. -/

@[expose] public section
namespace VG.Proof.Weierstrass

theorem hornerVal_eq_at (k d c : Nat) :
    hornerVal (fun i => (k.testBit i).toNat) d c = k/2^d%2^c := by
  have h := hornerVal_eq k (d+c) 0 c (by omega)
  simpa only [Nat.mul_zero,Nat.zero_add,show d+c-c=d by omega] using h

theorem hornerVal_window (k d c : Nat) :
    hornerVal (fun i => (k.testBit (d+i)).toNat) 0 c = k/2^d%2^c := by
  rw [hornerVal_congr (d := 0) (d' := d) (v' := fun i => (k.testBit i).toNat)
    (fun i _ => by rw [Nat.zero_add]),hornerVal_eq_at]

theorem topWindow_le {w J bits : Nat} (hJ : 1≤J) (hb : bits≤w*J) :
    bits-w*(J-1)≤w := by
  have e : w*(J-1)+w=w*J := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  omega

theorem windowBits_bounds {w J bits j : Nat} (hj : j<J)
    (hs : w*(J-1)≤bits) (hb : bits≤w*J) :
    let count := if j=J-1 then bits-w*(J-1) else w
    count≤w ∧ w*j+count≤bits ∧ (count=w ∨ w*j+count=bits) := by
  dsimp only
  by_cases h : j=J-1
  · simp only [h,↓reduceIte]
    have e : w*(J-1)+(bits-w*(J-1))=bits := Nat.add_sub_of_le hs
    exact ⟨topWindow_le (by omega) hb,by omega,.inr e⟩
  · rw [show (if j=J-1 then bits-w*(J-1) else w)=w by simp only [h,↓reduceIte]]
    refine ⟨Nat.le_refl _,?_,.inl rfl⟩
    calc
      w*j+w=w*(j+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ ≤ w*(J-1) := Nat.mul_le_mul_left w (by omega)
      _ ≤ bits := hs

theorem window_without_padding {w k j count bits : Nat}
    (hc : count≤w) (h : count=w ∨ w*j+count=bits) (hk : k<2^bits) :
    hornerVal (fun i => (k.testBit (w*j+i)).toNat) 0 count=combWin w k j := by
  rw [hornerVal_window,combWin]
  rcases h with rfl | h
  · rfl
  · have div : k/2^(w*j)<2^count := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      rw [← Nat.pow_add,show count+w*j=bits by omega]
      exact hk
    have div' : k/2^(w*j)<2^w :=
      Nat.lt_of_lt_of_le div (Nat.pow_le_pow_right (by decide) hc)
    rw [Nat.mod_eq_of_lt div,Nat.mod_eq_of_lt div']

end VG.Proof.Weierstrass
