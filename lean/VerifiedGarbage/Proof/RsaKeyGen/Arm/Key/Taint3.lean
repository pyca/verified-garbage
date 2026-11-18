module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Vals
public import VerifiedGarbage.Proof.RsaKeyGen.KeyOp

/-! ### `RsaKeyGen.Arm.Key.Result`, which the modules that import this one used -/

section

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
    exact ⟨h.1, by omega_using [h], by omega_using [this]⟩
  · exact ⟨rfl, by decide, by have := Nat.two_pow_pos (8 * P.K); omega⟩

theorem qx_spec [VG.Proof.Rsa.Arm.Keys.InvLaw] (pre : In P σ) : (qM P σ : Int) ∣ (qx P σ : Int) * qv P σ - qg P σ ∧ qx P σ < qM P σ ∧
    qg P σ = Nat.gcd (qv P σ) (qM P σ) := by
  have := pre.k1
  have hm := qM_odd P σ
  have p8 : 2 ^ (8 * P.K) + 3 ≤ 2 ^ (32 * P.W) := by
    have : 2 ^ (8 * P.K) * 2 ≤ 2 ^ (32 * P.W) := by
      rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by simp only [KP.W]; omega_using [])
    have : 4 ≤ 2 ^ (8 * P.K) := Nat.le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega_arith))
    omega_arith
  obtain ⟨g, d, l⟩ := ivr_spec (W := P.W) (a := qv P σ) hm.1 hm.2.1 (by have := qv_lt P σ; omega_using [p8, this]) (by omega_using [hm, p8])
  exact ⟨by unfold qx qg; exact d, l, g⟩

theorem qv_le_pv (P : KP) (σ : State) : qv P σ ≤ pv P σ := by
  unfold pv qv; split <;> omega_arith

/-- The result is `resv`. -/
theorem res_spec [VG.Proof.Rsa.Arm.Keys.InvLaw] (pre : In P σ) : res P σ = resv P σ := by
  have hx := qx_spec pre
  have key := keyFromPrimes_code (pLen := P.K) (e := P.e) (P₀ := P0 P σ) (Q₀ := Q0 P σ) (x := qx P σ)
    pre.k1 pre.k2 (P0_lt P σ) (Q0_lt P σ) pre.e_lt
    (by have := hx.1; rw [hx.2.2] at this; exact this) hx.2.1
  have lcmE : Nat.lcm (pv P σ - 1) (qv P σ - 1) = lv P σ := (lv_eq P σ).symm
  unfold res Proof.RsaKeyGen.keyOp
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
        have := Nat.one_lt_two_pow (n := 8 * P.K) (by have := pre.k1; omega_using [this]); omega
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
        rw [ite_eq_right (by omega_using [p3]), ite_eq_right (by omega_using [q2])]
        simp only [nv]
      · rw [ite_eq_right hm, ite_eq_right hm]

end

end VG.Proof.RsaKeyGen.Arm.Key

end

end

/-! # An RSA key on ARMv7: the pieces of the key the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key

-- `qInv`
theorem bitPo_taint : Cert (.block (bitOf sPo aP)) := ⟨_, by taint_decide⟩
theorem ltP3_taint : Cert (seqs (ltS sP3 aP aThree)) := ⟨_, by taint_decide⟩
theorem qg_taint : Cert (.block (andNotS sQg sP3 sPo)) := ⟨_, by taint_decide⟩
theorem selQM_taint : Cert (sel aTmp2 aThree aP sQg) := ⟨_, by taint_decide⟩
theorem q0_taint : Cert (copy 0 aQ) := ⟨_, by taint_decide⟩
theorem eqGq_taint : Cert (eqS sGq 1 aOne aTmp) := ⟨_, by taint_decide⟩
theorem qi_taint : Cert (copy aQi 3) := ⟨_, by taint_decide⟩

-- `dP` and `dQ`
theorem zPm_taint : Cert (eqS sZ aPm aZero aTmp) := ⟨_, by taint_decide⟩
theorem selPm1_taint : Cert (sel aTmp2 aPm aOne sZ) := ⟨_, by taint_decide⟩
theorem zQm_taint : Cert (eqS sZ aQm aZero aTmp) := ⟨_, by taint_decide⟩
theorem selQm1_taint : Cert (sel aTmp2 aQm aOne sZ) := ⟨_, by taint_decide⟩
theorem qdD_taint : Cert (copy aQd aD) := ⟨_, by taint_decide⟩
theorem dvT2_taint : Cert (copy aDv aTmp2) := ⟨_, by taint_decide⟩
theorem dpDr_taint : Cert (copy aDP aDr) := ⟨_, by taint_decide⟩
theorem dqDr_taint : Cert (copy aDQ aDr) := ⟨_, by taint_decide⟩

-- `n`
theorem myQ_taint : Cert (copy aMy aQ) := ⟨_, by taint_decide⟩
theorem mxP_taint : Cert (copy aMx aP) := ⟨_, by taint_decide⟩
theorem nMa_taint : Cert (copy aN aMa) := ⟨_, by taint_decide⟩

-- The mask
theorem ltTop_taint : Cert (seqs (ltS sTop aN aTop)) := ⟨_, by taint_decide⟩
theorem bitQo_taint : Cert (.block (bitOf sQo aQ)) := ⟨_, by taint_decide⟩
theorem ltE3_taint : Cert (seqs (ltS sE3 aE aThree)) := ⟨_, by taint_decide⟩
theorem ltEv_taint : Cert (seqs (ltS sEv aE aC33)) := ⟨_, by taint_decide⟩
theorem m1_taint : Cert (.block (andNotS sMask sTop sOk)) := ⟨_, by taint_decide⟩
theorem m2_taint : Cert (.block (andS sMask sMask sGq)) := ⟨_, by taint_decide⟩
theorem m3_taint : Cert (.block (andS sMask sMask sPo)) := ⟨_, by taint_decide⟩
theorem m4_taint : Cert (.block (andS sMask sMask sQo)) := ⟨_, by taint_decide⟩
theorem m5_taint : Cert (.block (andS sMask sMask sEo)) := ⟨_, by taint_decide⟩
theorem m6_taint : Cert (.block (andNotS sE3 sE3 sEv)) := ⟨_, by taint_decide⟩
theorem m7_taint : Cert (.block (andS sMask sMask sE3)) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Key
