module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Vals
public import VerifiedGarbage.Proof.RsaKeyGen.KeyOp

/-! # An RSA key on ARMv7: the result, as the body computes it

`qInv` (`qx`, with the gcd `qg`) modulo `qModP pv`, `dP` and `dQ` (by 1 for
`pm` or `qm` zero), `n`, and the mask of the checks (`maskv`): the result of
`vg_rsa_keygen_key` is `.inr ()` for `okv` and `d ≤ 2^(8 p_len)`, the key
under the mask, and a failure otherwise (`res_spec`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.RsaKeyGen

section
variable (P : KP) (σ : State)

/-- The modulus of `qInv`. -/
def qM : Nat := qModP (pv P σ)
def qx : Nat := (ivr P.W (qv P σ) (qM P σ)).2.2.2
def qg : Nat := (ivr P.W (qv P σ) (qM P σ)).2.1
def dPv : Nat := dv P σ % (if pm P σ = 0 then 1 else pm P σ)
def dQv : Nat := dv P σ % (if qm P σ = 0 then 1 else qm P σ)
def nv : Nat := pv P σ * qv P σ

/-- The mask of the checks, in the code's order. -/
def maskv : Bool :=
  (((((!decide (nv P σ < 2 ^ (16 * P.K - 1)) && okv P σ) && decide (qg P σ = 1)) && decide (pv P σ % 2 = 1)) &&
    decide (qv P σ % 2 = 1)) && decide (P.e % 2 = 1)) && (!decide (P.e < 3) && decide (P.e < 2 ^ 33))

/-- The outputs. -/
def outv : List (List Byte) :=
  [Spec.Rsa.i2osp (nv P σ) (2 * P.K), Spec.Rsa.i2osp (dv P σ) (2 * P.K), Spec.Rsa.i2osp (pv P σ) P.K,
    Spec.Rsa.i2osp (qv P σ) P.K, Spec.Rsa.i2osp (dPv P σ) P.K, Spec.Rsa.i2osp (dQv P σ) P.K,
    Spec.Rsa.i2osp (qx P σ) P.K]

/-- The result, as the body computes it. -/
def resv : Except Spec.RsaKeyGen.Failure (List (List Byte)) ⊕ Unit :=
  if (okv P σ && decide (dv P σ ≤ 2 ^ (8 * P.K))) = true then .inr ()
  else if maskv P σ = true then .inl (.ok (outv P σ)) else .inl (.error .internal)

end

section
variable {P : KP} {σ : State}

theorem qM_odd (P : KP) (σ : State) : qM P σ % 2 = 1 ∧ 1 < qM P σ ∧ qM P σ < 2 ^ (8 * P.K) + 3 := by
  unfold qM qModP
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
    have := pv_lt P σ
    exact ⟨h.1, by omega, by omega⟩
  · exact ⟨rfl, by decide, by have := Nat.two_pow_pos (8 * P.K); omega⟩

theorem qx_spec [VG.Proof.Rsa.Arm.Keys.InvLaw] (pre : In P σ) : (qM P σ : Int) ∣ (qx P σ : Int) * qv P σ - qg P σ ∧ qx P σ < qM P σ ∧
    qg P σ = Nat.gcd (qv P σ) (qM P σ) := by
  have := pre.k1
  have hm := qM_odd P σ
  have p8 : 2 ^ (8 * P.K) + 3 ≤ 2 ^ (32 * P.W) := by
    have : 2 ^ (8 * P.K) * 2 ≤ 2 ^ (32 * P.W) := by
      rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by simp only [KP.W]; omega)
    have : 4 ≤ 2 ^ (8 * P.K) := Nat.le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  obtain ⟨g, d, l⟩ := ivr_spec (W := P.W) (a := qv P σ) hm.1 hm.2.1 (by have := qv_lt P σ; omega) (by omega)
  exact ⟨by unfold qx qg; exact d, l, g⟩

theorem qv_le_pv (P : KP) (σ : State) : qv P σ ≤ pv P σ := by
  unfold pv qv; split <;> omega

/-- The result is `resv`. -/
theorem res_spec [VG.Proof.Rsa.Arm.Keys.InvLaw] (pre : In P σ) : res P σ = resv P σ := by
  have hx := qx_spec pre
  have key := keyFromPrimes_code (pLen := P.K) (e := P.e) (P₀ := P0 P σ) (Q₀ := Q0 P σ) (x := qx P σ)
    pre.k1 pre.k2 (P0_lt P σ) (Q0_lt P σ) pre.e_lt
    (by have := hx.1; rw [hx.2.2] at this; exact this) hx.2.1
  have lcmE : Nat.lcm (pv P σ - 1) (qv P σ - 1) = lv P σ := (lv_eq P σ).symm
  unfold res Spec.RsaKeyGen.keyOp
  rw [key]
  have hp : (if P0 P σ < Q0 P σ then Q0 P σ else P0 P σ) = pv P σ := rfl
  have hq : (if P0 P σ < Q0 P σ then P0 P σ else Q0 P σ) = qv P σ := rfl
  simp only [hp, hq, lcmE]
  obtain ⟨hs, hn⟩ := dv_spec pre
  unfold resv
  cases hok : okv P σ
  · rw [hn hok]
    have : maskv P σ = false := by unfold maskv; rw [hok]; simp
    simp [this]
  · rw [hs hok]
    dsimp only
    by_cases hsm : dv P σ ≤ 2 ^ (8 * P.K)
    · simp [hsm]
    · have h2 : 2 ≤ dv P σ := by
        have := Nat.one_lt_two_pow (n := 8 * P.K) (by have := pre.k1; omega); omega
      obtain ⟨p3, q2, -⟩ := VG.Proof.RsaKeyGen.primes_of_inverse (qv_le_pv P σ) (by rw [lcmE]; exact hs hok) h2
      have hmask : maskv P σ = (decide (2 ^ (16 * P.K - 1) ≤ pv P σ * qv P σ) &&
          decide ((qv P σ).gcd (qModP (pv P σ)) = 1) && decide (pv P σ % 2 = 1) && decide (qv P σ % 2 = 1) &&
          Spec.Rsa.exponentValid P.e) := by
        unfold maskv Spec.Rsa.exponentValid nv
        rw [hok, hx.2.2]
        unfold qM
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
          beq_iff_eq, Nat.not_lt]
        simp only [and_assoc]
      rw [ite_eq_right hsm, ← hmask]
      simp only [hsm, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hm : maskv P σ = true
      · rw [ite_eq_left hm, ite_eq_left hm]
        unfold outv dPv dQv pm qm
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [nv]
      · rw [ite_eq_right hm, ite_eq_right hm]

end

end VG.Proof.RsaKeyGen.Arm.Key
