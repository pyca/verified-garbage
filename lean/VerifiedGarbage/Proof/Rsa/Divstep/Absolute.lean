module

public import VerifiedGarbage.Proof.Divstep.Tc32Words

/-! # Recovering an absolute value from its low-word residue -/

@[expose] public section
namespace VG.Proof.Rsa.Divstep

 theorem signed_residue {R W : Int} {x : Int} (hR : 0<R) (hx1 : -R<x) (hx2 : x<R)
    (hW0 : 0≤W) (hW1 : W<R) (hc : W%R=x%R) :
    W=x+if x<0 then R else 0 := by
  have h : W ≡ x [ZMOD R] := hc
  obtain ⟨c,hc'⟩ := h.dvd
  have c1 : c≤0 := by
    by_contra hn
    have : R*1≤R*c := mul_le_mul_of_nonneg_left (by omega) hR.le
    linarith
  have c2 : -1≤c := by
    by_contra hn
    have : R*c≤R*(-2) := mul_le_mul_of_nonneg_left (by omega) hR.le
    linarith
  split
  · have : c = -1 := by
      by_contra hn
      have : c=0 := by omega
      subst this
      linarith
    subst this
    linarith
  · have : c=0 := by
      by_contra hn
      have : c = -1 := by omega
      subst this
      linarith
    subst this
    linarith

theorem abs_select {R lo neg : Nat} {x : Int} (hR : 0<R)
    (hb : |x| < R) (hlo : lo<R)
    (hc : (lo : Int)%(R : Int)=x%(R : Int))
    (sub : ∃ c : Bool,neg+lo=R*c.toNat) :
    (if x<0 then neg else lo)=x.natAbs := by
  have b := abs_lt.mp hb
  have e := signed_residue (by exact_mod_cast hR) b.1 b.2 (Int.natCast_nonneg _) (by exact_mod_cast hlo) hc
  obtain ⟨c,cs⟩ := sub
  have absx : (x.natAbs : Int)=|x| := Int.natCast_natAbs x
  by_cases hx : x<0
  · rw [ite_eq_left hx] at e ⊢
    have c1 : c=true := by
      cases c <;> simp_all only [Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one]
      omega
    rw [c1] at cs
    simp only [Bool.toNat_true,Nat.mul_one] at cs
    rw [abs_of_neg hx] at absx
    omega
  · rw [ite_eq_right hx] at e ⊢
    rw [abs_of_nonneg (by omega)] at absx
    omega

end VG.Proof.Rsa.Divstep
