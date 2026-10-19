module

public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Rsa.KeyParts
public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # `vg_rsa_crt_values` on 32-bit targets: the checks are `crtKey`

`crtKey_masked`: with the mask of the checks computed as `vg_rsa_crt_values`
computes them (`p` odd, `n / p = q`, `n mod p = 0`, and the gcd that
`inverse` finds modulo `p | 1` is 1), `crtKey` is the values computed if the
mask is set, and nothing otherwise.
-/

@[expose] public section

namespace VG.Proof.Rsa.CrtValues
open VG.Spec.Rsa

/-- `p q = n` for an odd `n`, as the checks check it. -/
theorem pq_iff {N P Q : Nat} (hN : N % 2 = 1) :
    (P % 2 = 1 ∧ N / P = Q ∧ N % P = 0) ↔ P * Q = N := by
  constructor
  · rintro ⟨_, hq, hr⟩
    have := Nat.div_add_mod N P
    rw [hq, hr, Nat.add_zero] at this
    exact this
  · intro h
    have hp : P % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one P with hP | hP
      · rw [← h, Nat.mul_mod, hP, Nat.zero_mul] at hN; exact absurd hN (by decide)
      · exact hP
    have hP0 : 0 < P := by omega
    refine ⟨hp, ?_, ?_⟩
    · rw [← h, Nat.mul_div_cancel_left _ hP0]
    · rw [← h, Nat.mul_mod_right]

theorem odd_of_mul {P Q N : Nat} (h : P * Q = N) (hN : N % 2 = 1) : Q % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one Q with hQ | hQ
  · rw [← h, Nat.mul_mod, hQ, Nat.mul_zero] at hN; exact absurd hN (by decide)
  · exact hQ

theorem crtKey_masked {nb pb qb db : List Byte} (hv : modulusValid (os2ip nb) nb.length = true)
    (hp : pb.length < nb.length) (hq : qb.length < nb.length) {X₁ X₂ V R₂ R₃ X : Nat}
    (h₁ : 0 < os2ip pb → X₁ = os2ip nb / os2ip pb ∧ X₂ = os2ip nb % os2ip pb)
    (h₂ : 1 < 2 * (os2ip pb / 2) + 1 → V = Nat.gcd (os2ip qb) (2 * (os2ip pb / 2) + 1) ∧
      ((2 * (os2ip pb / 2) + 1 : Nat) : Int) ∣ (X : Int) * os2ip qb - V ∧ X < 2 * (os2ip pb / 2) + 1)
    (h₃ : 0 < 2 * (os2ip pb / 2) → R₂ = os2ip db % (2 * (os2ip pb / 2)))
    (h₄ : 0 < 2 * (os2ip qb / 2) → R₃ = os2ip db % (2 * (os2ip qb / 2))) :
    crtKey nb pb qb db = if maskOf (os2ip pb) (os2ip qb) X₁ X₂ V then
      some (i2osp (R₂ % 2 ^ (8 * pb.length)) pb.length, i2osp (R₃ % 2 ^ (8 * qb.length)) qb.length,
        i2osp (X % 2 ^ (8 * pb.length)) pb.length) else none := by
  have hv' := hv
  simp only [modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv'
  obtain ⟨⟨⟨hodd, _⟩, _⟩, hlow⟩ := hv'
  have pl := VG.Proof.Rsa.lt_of_os2ip pb
  have ql := VG.Proof.Rsa.lt_of_os2ip qb
  have pk : 256 ^ pb.length ≤ 256 ^ (nb.length - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have qk : 256 ^ qb.length ≤ 256 ^ (nb.length - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have e256 : ∀ k, (256 : Nat) ^ k = 2 ^ (8 * k) := fun k => by rw [Nat.pow_mul]
  unfold crtKey
  dsimp only
  generalize os2ip nb = N at *
  generalize os2ip pb = P at *
  generalize os2ip qb = Q at *
  by_cases hpq : P * Q = N
  · have p2 := VG.Proof.Rsa.factor_ge_two hpq (Nat.lt_of_lt_of_le ql qk) hlow
    have q2 := VG.Proof.Rsa.factor_ge_two (n := N) (q := P) (by rw [Nat.mul_comm]; exact hpq)
      (Nat.lt_of_lt_of_le pl pk) hlow
    have ⟨podd, hdiv, hmod⟩ := (pq_iff hodd).mpr hpq
    have qodd := odd_of_mul hpq hodd
    have eM : 2 * (P / 2) + 1 = P := by omega
    obtain ⟨e1, e2⟩ := h₁ (by omega)
    rw [eM] at h₂
    obtain ⟨eV, dv, xl⟩ := h₂ (by omega)
    simp only [hv, hpq, and_self, ↓reduceIte]
    have eR₂ := h₃ (by omega)
    have eR₃ := h₄ (by omega)
    rw [show 2 * (P / 2) = P - 1 by omega] at eR₂
    rw [show 2 * (Q / 2) = Q - 1 by omega] at eR₃
    by_cases hg : Nat.gcd Q P = 1
    · have hm : maskOf P Q X₁ X₂ V = true := by
        simp only [maskOf, decide_eq_true_eq]; refine ⟨podd, ?_, ?_, ?_⟩ <;> omega
      simp only [hm, ↓reduceIte]
      rw [eV, hg] at dv
      simp only [crtValues, VG.Proof.Rsa.inverse_eq (by omega) xl dv, Option.map_some]
      rw [eR₂, eR₃]
      have m2 : (os2ip db % (P - 1)) % 2 ^ (8 * pb.length) = os2ip db % (P - 1) := by
        rw [← e256]; exact Nat.mod_eq_of_lt (by have := Nat.mod_lt (os2ip db) (show 0 < P - 1 by omega); omega)
      have m3 : (os2ip db % (Q - 1)) % 2 ^ (8 * qb.length) = os2ip db % (Q - 1) := by
        rw [← e256]; exact Nat.mod_eq_of_lt (by have := Nat.mod_lt (os2ip db) (show 0 < Q - 1 by omega); omega)
      have mx : X % 2 ^ (8 * pb.length) = X := by rw [← e256]; exact Nat.mod_eq_of_lt (by omega)
      rw [m2, m3, mx]
    · have hm : maskOf P Q X₁ X₂ V = false := by
        simp only [maskOf, decide_eq_false_iff_not]; intro ⟨_, _, _, h1⟩; exact hg (by rw [← eV]; exact h1)
      rw [hm]
      simp only [crtValues, VG.Proof.Rsa.inverse_none hg, Option.map_none]
      rfl
  · simp only [hpq, and_false, ↓reduceIte]
    have hm : maskOf P Q X₁ X₂ V = false := by
      simp only [maskOf, decide_eq_false_iff_not]
      intro ⟨podd, a, b, _⟩
      obtain ⟨e1, e2⟩ := h₁ (by omega)
      exact hpq ((pq_iff hodd).mp ⟨podd, by omega, by omega⟩)
    rw [hm]; rfl

end VG.Proof.Rsa.CrtValues
