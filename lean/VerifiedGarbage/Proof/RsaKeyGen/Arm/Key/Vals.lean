module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Inv
public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.KeyInv
import VerifiedGarbage.Proof.Rsa.Arm.RvProd
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # An RSA key on ARMv7: the numbers the body computes

As functions of the state `σ` the body starts from: the primes ordered
(`pv ≥ qv`), `pm = pv − 1` and `qm = qv − 1`, the halving (`hv`), the gcd
(`gv`) and `lv = lcm(pm, qm)` (`lv_eq`); `d` and the flag of its existence by
`e`'s case (`dv`, `okv`), which are `Rsa.inverse e lv` (`dv_spec`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.RsaKeyGen
open VG.Proof.Rsa.Arm.Recover (sub32)

section
variable (P : KP) (σ : State)

abbrev P0 : Nat := Spec.Rsa.os2ip (pB P σ)
abbrev Q0 : Nat := Spec.Rsa.os2ip (qB P σ)

def pv : Nat := if P0 P σ < Q0 P σ then Q0 P σ else P0 P σ
def qv : Nat := if P0 P σ < Q0 P σ then P0 P σ else Q0 P σ
def pm : Nat := pv P σ - 1
def qm : Nat := qv P σ - 1

/-- The halving of `(pm, qm, pm qm)`. -/
def hv : Nat × Nat × Nat := halveIter (8 * P.K) (pm P σ, qm P σ, pm P σ * qm P σ)

/-- `u` and `v` swapped so that `v` is odd if one is. -/
def u2 : Nat := if (hv P σ).2.1 % 2 = 0 then (hv P σ).2.1 else (hv P σ).1
def v2 : Nat := if (hv P σ).2.1 % 2 = 0 then (hv P σ).1 else (hv P σ).2.1

/-- `gcd(u, v)`, 1 for `v < 2`. -/
def gv : Nat := if v2 P σ < 2 then 1 else (ivr P.W (u2 P σ) (v2 P σ)).2.1

/-- `lcm(pm, qm)`. -/
def lv : Nat := (hv P σ).2.2 / gv P σ

/-- The modulus of an even `e`'s inverse: `lv` if it is odd and at least 3. -/
def mE : Nat := if lv P σ % 2 = 1 ∧ ¬ lv P σ < 3 then lv P σ else 3

/-- `d`, by `e`'s case. -/
def dv : Nat :=
  if P.e = 0 then 0 else if P.e = 1 then 1 else if P.e % 2 = 1 then
    ((1 + sub32 P.W P.e (ivr P.W (lv P σ) P.e).2.2.2 % 2 ^ 64 * lv P σ) % 2 ^ (32 * P.W - 1)) / P.e
  else (ivr P.W P.e (mE P σ)).2.2.2

/-- Whether `d` exists, by `e`'s case. -/
def okv : Bool :=
  if P.e = 0 then false else if P.e = 1 then !decide (lv P σ = 1) else if P.e % 2 = 1 then
    (!decide (lv P σ < 2) && decide ((ivr P.W (lv P σ) P.e).2.1 = 1))
  else (!decide (lv P σ < 3) && decide (lv P σ % 2 = 1)) && decide ((ivr P.W P.e (mE P σ)).2.1 = 1)

end

section
variable {P : KP} {σ : State}

theorem In.e_lt (pre : In P σ) : P.e < 2 ^ 64 := by
  have := VG.Proof.Rsa.Arm.Recover.bytes_lt σ.mem (State.addr P.eP) P.el
  rw [pre.eB] at this
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := pre.el2; omega_arith))

theorem P0_lt (P : KP) (σ : State) : P0 P σ < 2 ^ (8 * P.K) := VG.Proof.Rsa.Arm.Recover.bytes_lt _ _ _
theorem Q0_lt (P : KP) (σ : State) : Q0 P σ < 2 ^ (8 * P.K) := VG.Proof.Rsa.Arm.Recover.bytes_lt _ _ _

theorem pv_lt (P : KP) (σ : State) : pv P σ < 2 ^ (8 * P.K) := by
  unfold pv; split <;> [exact Q0_lt P σ; exact P0_lt P σ]

theorem qv_lt (P : KP) (σ : State) : qv P σ < 2 ^ (8 * P.K) := by
  unfold qv; split <;> [exact P0_lt P σ; exact Q0_lt P σ]

theorem pm_lt (P : KP) (σ : State) : pm P σ < 2 ^ (8 * P.K) := by
  have := pv_lt P σ; unfold pm; omega_arith

theorem qm_lt (P : KP) (σ : State) : qm P σ < 2 ^ (8 * P.K) := by
  have := qv_lt P σ; unfold qm; omega_arith

/-- The bounds of the working space's numbers. -/
theorem In.k16 (pre : In P σ) : 16 * P.K + 64 < 32 * P.W - 1 := by
  have := pre.k1; simp only [KP.W]; omega_arith

theorem phi_lt (P : KP) (σ : State) : pm P σ * qm P σ < 2 ^ (16 * P.K) := by
  rw [show 16 * P.K = 8 * P.K + 8 * P.K by omega_arith, Nat.pow_add]
  exact Nat.mul_lt_mul'' (pm_lt P σ) (qm_lt P σ)

/-- The halving keeps the numbers below their bounds. -/
theorem hv_le (P : KP) (σ : State) :
    (hv P σ).1 ≤ pm P σ ∧ (hv P σ).2.1 ≤ qm P σ ∧ (hv P σ).2.2 ≤ pm P σ * qm P σ := by
  obtain ⟨k, ha, hb, hf⟩ := halveIter_inv (8 * P.K) (a := pm P σ) (b := qm P σ)
    (st := (pm P σ, qm P σ, pm P σ * qm P σ)) ⟨0, by simp, by simp, by simp⟩
  unfold hv
  generalize halveIter (8 * P.K) (pm P σ, qm P σ, pm P σ * qm P σ) = st at ha hb hf
  obtain ⟨u, v, f⟩ := st
  dsimp only at ha hb hf ⊢
  have p : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]; exact Nat.le_mul_of_pos_left _ p
  · rw [hb]; exact Nat.le_mul_of_pos_left _ p
  · rw [ha, hb, hf]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ p)

/-- The halving's `u` and `v` are below `2^(32 W)`. -/
theorem hv_lt (P : KP) (σ : State) : (hv P σ).1 < 2 ^ (32 * P.W) ∧ (hv P σ).2.1 < 2 ^ (32 * P.W) := by
  have hle := hv_le P σ
  have := Nat.pow_le_pow_right (n := 2) (by decide) (show 8 * P.K ≤ 32 * P.W by simp only [KP.W]; omega_arith)
  have := pm_lt P σ; have := qm_lt P σ
  omega_arith

/-- `lv = lcm(pm, qm)`. -/
theorem lv_eq [VG.Proof.Rsa.Arm.Keys.InvLaw] (P : KP) (σ : State) : lv P σ = Nat.lcm (pm P σ) (qm P σ) := by
  have L := lcm_eq (K := 8 * P.K) (pm_lt P σ) (qm_lt P σ)
  have lt := hv_lt P σ
  unfold lv gv u2 v2
  unfold hv at lt ⊢
  generalize halveIter (8 * P.K) (pm P σ, qm P σ, pm P σ * qm P σ) = st at L lt ⊢
  obtain ⟨u, v, f⟩ := st
  dsimp only at L lt ⊢
  obtain ⟨hodd, hl⟩ := L
  rw [hl]
  congr 1
  by_cases hv0 : v % 2 = 0
  · simp only [hv0, ↓reduceIte] at hodd ⊢
    by_cases hu : u < 2
    · rw [ite_eq_left hu, ite_eq_left (show u ≤ 1 by omega_arith)]
    · rw [ite_eq_right hu, ite_eq_right (show ¬ u ≤ 1 by omega_arith)]
      exact (ivr_spec (hodd (by omega_arith)) (by omega_arith) lt.2 lt.1).1
  · simp only [hv0, ↓reduceIte] at hodd ⊢
    by_cases hu : v < 2
    · rw [ite_eq_left hu, ite_eq_left (show v ≤ 1 by omega_arith)]
    · rw [ite_eq_right hu, ite_eq_right (show ¬ v ≤ 1 by omega_arith)]
      exact (ivr_spec (hodd (by omega_arith)) (by omega_arith) lt.1 lt.2).1

theorem lv_lt (P : KP) (σ : State) : lv P σ < 2 ^ (16 * P.K) := by
  have := (hv_le P σ).2.2
  have := phi_lt P σ
  have : lv P σ ≤ (hv P σ).2.2 := Nat.div_le_self _ _
  omega_arith

theorem sub32_le {W a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ (32 * W)) : sub32 W a b = a - b := by
  unfold sub32
  rw [show a + 2 ^ (32 * W) - b = (a - b) + 2 ^ (32 * W) by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]

/-- `d` and its flag are the inverse of the specification. -/
theorem dv_spec [VG.Proof.Rsa.Arm.Keys.InvLaw] (pre : In P σ) :
    (okv P σ = true → Spec.Rsa.inverse P.e (lv P σ) = some (dv P σ)) ∧
      (okv P σ = false → Spec.Rsa.inverse P.e (lv P σ) = none) := by
  have he := pre.e_lt
  have hl := lv_lt P σ
  have k16 := pre.k16
  have p16 : 2 ^ (16 * P.K) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have p64 : 2 ^ 64 ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  unfold okv dv
  by_cases e0 : P.e = 0
  · simp only [e0, ↓reduceIte]
    exact ⟨fun h => absurd h (by decide), fun _ => inverse_zero _⟩
  by_cases e1 : P.e = 1
  · simp only [e1, ↓reduceIte]
    rw [inverse_one]
    by_cases h : lv P σ = 1 <;> simp [h]
  simp only [e0, e1, ↓reduceIte]
  by_cases eo : P.e % 2 = 1
  · simp only [eo, ↓reduceIte]
    obtain ⟨g, dvd, xlt⟩ := ivr_spec (W := P.W) (a := lv P σ) eo (by omega_arith) (by omega_arith) (by omega_arith)
    generalize ivr P.W (lv P σ) P.e = r at g dvd xlt ⊢
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h
      obtain ⟨h2, g1⟩ := h
      rw [g1] at dvd
      rw [g] at g1
      obtain ⟨-, inv⟩ := inverse_odd_exact (e := P.e) (L := lv P σ) (by omega_arith) (by omega_arith)
        (by exact_mod_cast dvd) xlt
      rw [inv, sub32_le (by omega_arith) (by omega_arith), Nat.mod_eq_of_lt (a := P.e - r.2.2.2) (by omega_arith)]
      congr 2
      have : (P.e - r.2.2.2) * lv P σ < 2 ^ 64 * 2 ^ (16 * P.K) := Nat.mul_lt_mul'' (by omega_arith) hl
      have : 2 ^ 64 * 2 ^ (16 * P.K) * 2 ≤ 2 ^ (32 * P.W - 1) := by
        rw [← Nat.pow_add, ← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
      rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mul_comm]
      omega_arith
    · simp only [Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at h
      refine inverse_odd_none' (by omega_arith) fun ⟨h2, h1⟩ => ?_
      rcases h with h | h
      · omega_arith
      · exact h (by rw [g]; exact h1)
  · simp only [eo, ↓reduceIte]
    have heven : P.e % 2 = 0 := by omega_arith
    have mo : mE P σ % 2 = 1 ∧ 1 < mE P σ ∧ mE P σ < 2 ^ (32 * P.W) := by
      unfold mE; split
      · rename_i h; exact ⟨h.1, by omega_arith, by omega_arith⟩
      · exact ⟨rfl, by decide, by omega_arith⟩
    obtain ⟨g, dvd, xlt⟩ := ivr_spec (W := P.W) (a := P.e) mo.1 mo.2.1 (by omega_arith) mo.2.2
    generalize ivr P.W P.e (mE P σ) = r at g dvd xlt ⊢
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h
      obtain ⟨⟨h3, ho⟩, g1⟩ := h
      have hm : mE P σ = lv P σ := by unfold mE; rw [ite_eq_left ⟨ho, h3⟩]
      rw [hm] at g dvd xlt
      rw [g1] at dvd
      exact VG.Proof.Rsa.inverse_eq (by omega_arith) xlt (by exact_mod_cast dvd)
    · simp only [Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at h
      refine inverse_even_none' heven fun ⟨ho, h3, h1⟩ => ?_
      have hm : mE P σ = lv P σ := by unfold mE; rw [ite_eq_left ⟨ho, by omega_arith⟩]
      rcases h with (h | h) | h
      · omega_arith
      · exact h ho
      · rw [hm] at g; exact h (by rw [g]; exact h1)

end

end VG.Proof.RsaKeyGen.Arm.Key
