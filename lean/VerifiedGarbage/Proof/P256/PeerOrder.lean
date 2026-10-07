import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.Weierstrass.PointCard
import VerifiedGarbage.Proof.Weierstrass.PeerOrder

/-! Every nonzero P-256 peer has prime order n, not just the generator. -/
namespace VG.Proof.P256
open Spec.Weierstrass Weierstrass

theorem generator_addOrderOf : addOrderOf (toW good (G Spec.P256.curve)) = Spec.P256.curve.n := by
  apply addOrderOf_eq_prime
  · rw [← toW_mul good onCurve_G, mul_n law]
    rfl
  · intro h
    have he := toW_inj good onCurve_G (show onCurve Spec.P256.curve .infinity = true from rfl) h
    cases he

/-- The cardinal is a positive multiple of n below 3n; the multiple 2 is excluded
by the absence of two-torsion. This avoids needing the Hasse bound. -/
theorem card_points : Nat.card (wcC Spec.P256.curve).Point = Spec.P256.curve.n := by
  have hd : Spec.P256.curve.n ∣ Nat.card (wcC Spec.P256.curve).Point := by
    rw [← generator_addOrderOf]
    exact addOrderOf_dvd_natCard _
  have hb := card_points_le (C := Spec.P256.curve)
  have hlt : Nat.card (wcC Spec.P256.curve).Point < Spec.P256.curve.n * 3 :=
    lt_of_le_of_lt hb (by decide +kernel)
  have hpos : 0 < Nat.card (wcC Spec.P256.curve).Point := Nat.card_pos
  obtain ⟨k, hk⟩ := hd
  rw [hk] at hlt hpos
  have hklt : k < 3 := (Nat.mul_lt_mul_left n_prime.pos).mp hlt
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp only [hk0, Nat.mul_zero, Nat.lt_irrefl] at hpos
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with h1 | h2
  · simpa only [h1, Nat.mul_one] using hk
  · exact False.elim (two_not_dvd_card_points good ⟨Spec.P256.curve.n, by
      rw [hk, h2, Nat.mul_comm]⟩)

theorem peer_addOrderOf (P : (wcC Spec.P256.curve).Point) (hP : P ≠ 0) :
    addOrderOf P = Spec.P256.curve.n := by
  have hd := addOrderOf_dvd_natCard P
  rw [card_points] at hd
  rcases n_prime.eq_one_or_self_of_dvd _ hd with h1 | hn
  · apply False.elim ∘ hP
    have hz := addOrderOf_nsmul_eq_zero P
    simpa only [h1, one_nsmul] using hz
  · exact hn

theorem mul_n_peer {P : Point Spec.P256.curve} (hP : onCurve Spec.P256.curve P = true) :
    mul Spec.P256.curve.n P = .infinity := by
  apply toW_inj good (law.onCurve_mul hP _) (show onCurve Spec.P256.curve .infinity = true from rfl)
  rw [toW_mul good hP, ← card_points]
  exact card_nsmul_eq_zero'

theorem peer_zmul_dvd {P : Point Spec.P256.curve} (hP : onCurve Spec.P256.curve P = true)
    (hne : P ≠ .infinity) {a b : Int} (h : zmul a P = zmul b P) :
    (Spec.P256.curve.n : Int) ∣ a - b := by
  have hf : GroupRep Spec.P256.curve (wcC Spec.P256.curve).Point (toW good) := by
    refine ⟨toW_add good, fun hQ k => ?_, toW_neg good, toW_inj good⟩
    rw [toW_mul good hQ, ← natCast_zsmul]
  have horder := peer_addOrderOf (toW good P) (fun he =>
    hne (toW_inj good hP (show onCurve Spec.P256.curve .infinity = true from rfl) he))
  have he := congrArg (toW good) h
  rw [law.group_zmul hf hP, law.group_zmul hf hP] at he
  rw [← horder]
  exact addOrderOf_dvd_sub_iff_zsmul_eq_zsmul.mpr he

theorem peerOrder : PeerOrder Spec.P256.curve := ⟨mul_n_peer, peer_zmul_dvd⟩

end VG.Proof.P256
