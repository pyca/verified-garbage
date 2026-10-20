module

public import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM: the layers of the NTT, coefficient by coefficient

Each coefficient after a whole layer of `NTT` (`nttLayer_get`) or `NTT⁻¹`
(`nttInvLayer_get`), for implementations that compute a layer on lanes in
any order, and `nttL j f` (`nttInvL j f`), `f` after the first `j` layers:
`ntt f = nttL 7 f` (`ntt_eq_nttL`), `nttInv f` is `nttInvL 7 f` times 3303
(`nttInv_eq_nttInvL`).
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec.MlKem

private theorem div_mod_block {i d b : Nat} (h1 : d * b ≤ i) (h2 : i < d * b + d) :
    i / d = b ∧ i % d = i - d * b := by
  have hq : i / d = b := by
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [Nat.mul_comm]; exact h1
    · rw [Nat.succ_mul, Nat.mul_comm]; exact h2
  refine ⟨hq, ?_⟩
  have := Nat.div_add_mod i d
  rw [hq] at this
  omega

/-- Each coefficient after the first `b` blocks of the layer with `len`. -/
theorem nttLayerN_get (f : Poly) {len : Nat} (hlen : 0 < len) {b : Nat} (hb : 2 * len * b ≤ 256)
    {i : Nat} (hi : i < 256) :
    (nttLayerN f len b)[i]! =
      if i < 2 * len * b then
        if i % (2 * len) < len then f[i]! + zeta (128 / len + i / (2 * len)) * f[i + len]!
        else f[i - len]! - zeta (128 / len + i / (2 * len)) * f[i]!
      else f[i]! := by
  induction b generalizing i with
  | zero => rw [nttLayerN_zero, ite_eq_right (by omega)]
  | succ b ih =>
    have e : 2 * len * (b + 1) = 2 * len * b + 2 * len := Nat.mul_succ _ _
    rw [e] at hb ⊢
    generalize hS : 2 * len * b = S at hb ih ⊢
    rw [nttLayerN_succ, hS, nttBlock_get _ hlen (by rw [n_eq]; omega) (by rw [n_eq]; exact hi)]
    have ih' : ∀ j, S ≤ j → j < 256 → (nttLayerN f len b)[j]! = f[j]! := fun j h1 h2 => by
      rw [ih (by omega) h2, ite_eq_right (show ¬ j < S by omega)]
    by_cases c1 : i < S
    · rw [ite_eq_right (show ¬ (S ≤ i ∧ i < S + len) by omega),
        ite_eq_right (show ¬ (S + len ≤ i ∧ i < S + 2 * len) by omega), ih (by omega) hi, ite_eq_left c1,
        ite_eq_left (show i < S + 2 * len by omega)]
    · by_cases c2 : i < S + len
      · obtain ⟨dq, dm⟩ := div_mod_block (i := i) (d := 2 * len) (b := b) (by omega) (by omega)
        rw [ite_eq_left (show S ≤ i ∧ i < S + len from ⟨by omega, c2⟩),
          ite_eq_left (show i < S + 2 * len by omega), ite_eq_left (show i % (2 * len) < len by omega), dq,
          ih' i (by omega) hi, ih' (i + len) (by omega) (by omega)]
      · by_cases c3 : i < S + 2 * len
        · obtain ⟨dq, dm⟩ := div_mod_block (i := i) (d := 2 * len) (b := b) (by omega) (by omega)
          rw [ite_eq_right (show ¬ (S ≤ i ∧ i < S + len) by omega),
            ite_eq_left (show S + len ≤ i ∧ i < S + 2 * len from ⟨by omega, c3⟩), ite_eq_left c3,
            ite_eq_right (show ¬ i % (2 * len) < len by omega), dq, ih' i (by omega) hi,
            ih' (i - len) (by omega) (by omega)]
        · rw [ite_eq_right (show ¬ (S ≤ i ∧ i < S + len) by omega),
            ite_eq_right (show ¬ (S + len ≤ i ∧ i < S + 2 * len) by omega), ite_eq_right c3, ih' i (by omega) hi]

/-- Each coefficient after the layer with `len`. -/
theorem nttLayer_get (f : Poly) {len : Nat} (hlen : 0 < len) (hl : 2 * len * (128 / len) = 256)
    {i : Nat} (hi : i < 256) :
    (nttLayer f len)[i]! =
      if i % (2 * len) < len then f[i]! + zeta (128 / len + i / (2 * len)) * f[i + len]!
      else f[i - len]! - zeta (128 / len + i / (2 * len)) * f[i]! := by
  rw [nttLayer, nttLayerN_get f hlen (by omega) hi, ite_eq_left (by omega)]

/-- Each coefficient after the first `b` blocks of the inverse layer with `len`. -/
theorem nttInvLayerN_get (f : Poly) {len : Nat} (hlen : 0 < len) {b : Nat} (hb : 2 * len * b ≤ 256)
    {i : Nat} (hi : i < 256) :
    (nttInvLayerN f len b)[i]! =
      if i < 2 * len * b then
        if i % (2 * len) < len then f[i]! + f[i + len]!
        else zeta (256 / len - 1 - i / (2 * len)) * (f[i]! - f[i - len]!)
      else f[i]! := by
  induction b generalizing i with
  | zero => rw [nttInvLayerN_zero, ite_eq_right (by omega)]
  | succ b ih =>
    have e : 2 * len * (b + 1) = 2 * len * b + 2 * len := Nat.mul_succ _ _
    rw [e] at hb ⊢
    generalize hS : 2 * len * b = S at hb ih ⊢
    rw [nttInvLayerN_succ, hS, nttInvBlock_get _ hlen (by rw [n_eq]; omega) (by rw [n_eq]; exact hi)]
    have ih' : ∀ j, S ≤ j → j < 256 → (nttInvLayerN f len b)[j]! = f[j]! := fun j h1 h2 => by
      rw [ih (by omega) h2, ite_eq_right (show ¬ j < S by omega)]
    by_cases c1 : i < S
    · rw [ite_eq_right (show ¬ (S ≤ i ∧ i < S + len) by omega),
        ite_eq_right (show ¬ (S + len ≤ i ∧ i < S + 2 * len) by omega), ih (by omega) hi, ite_eq_left c1,
        ite_eq_left (show i < S + 2 * len by omega)]
    · by_cases c2 : i < S + len
      · obtain ⟨dq, dm⟩ := div_mod_block (i := i) (d := 2 * len) (b := b) (by omega) (by omega)
        rw [ite_eq_left (show S ≤ i ∧ i < S + len from ⟨by omega, c2⟩),
          ite_eq_left (show i < S + 2 * len by omega), ite_eq_left (show i % (2 * len) < len by omega),
          ih' i (by omega) hi, ih' (i + len) (by omega) (by omega)]
      · by_cases c3 : i < S + 2 * len
        · obtain ⟨dq, dm⟩ := div_mod_block (i := i) (d := 2 * len) (b := b) (by omega) (by omega)
          rw [ite_eq_right (show ¬ (S ≤ i ∧ i < S + len) by omega),
            ite_eq_left (show S + len ≤ i ∧ i < S + 2 * len from ⟨by omega, c3⟩), ite_eq_left c3,
            ite_eq_right (show ¬ i % (2 * len) < len by omega), dq, ih' i (by omega) hi,
            ih' (i - len) (by omega) (by omega)]
        · rw [ite_eq_right (show ¬ (S ≤ i ∧ i < S + len) by omega),
            ite_eq_right (show ¬ (S + len ≤ i ∧ i < S + 2 * len) by omega), ite_eq_right c3, ih' i (by omega) hi]

/-- Each coefficient after the inverse layer with `len`. -/
theorem nttInvLayer_get (f : Poly) {len : Nat} (hlen : 0 < len) (hl : 2 * len * (128 / len) = 256)
    {i : Nat} (hi : i < 256) :
    (nttInvLayer f len)[i]! =
      if i % (2 * len) < len then f[i]! + f[i + len]!
      else zeta (256 / len - 1 - i / (2 * len)) * (f[i]! - f[i - len]!) := by
  rw [nttInvLayer, nttInvLayerN_get f hlen (by omega) hi, ite_eq_left (by omega)]

/-! ## The first `j` layers -/

/-- `f` after the first `j` layers of `NTT`. -/
def nttL (j : Nat) (f : Poly) : Poly := (nttLens.take j).foldl nttLayer f

/-- `f` after the first `j` layers of `NTT⁻¹`, before the multiplication by 3303. -/
def nttInvL (j : Nat) (f : Poly) : Poly := (nttInvLens.take j).foldl nttInvLayer f

theorem nttL_zero (f : Poly) : nttL 0 f = f := rfl

theorem nttInvL_zero (f : Poly) : nttInvL 0 f = f := rfl

theorem nttL_succ (f : Poly) {j : Nat} (hj : j < 7) :
    nttL (j + 1) f = nttLayer (nttL j f) (128 >>> j) := by
  rw [nttL, nttL, List.take_add_one, List.foldl_append]
  have : nttLens[j]? = some (128 >>> j) := by
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl
  rw [this]; rfl

theorem nttInvL_succ (f : Poly) {j : Nat} (hj : j < 7) :
    nttInvL (j + 1) f = nttInvLayer (nttInvL j f) (2 <<< j) := by
  rw [nttInvL, nttInvL, List.take_add_one, List.foldl_append]
  have : nttInvLens[j]? = some (2 <<< j) := by
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl
  rw [this]; rfl

theorem ntt_eq_nttL (f : Poly) : ntt f = nttL 7 f := by
  rw [ntt_eq_layers]; rfl

theorem nttInv_eq_nttInvL (f : Poly) : nttInv f = (nttInvL 7 f).map (· * 3303) := by
  rw [nttInv_eq_layers]; rfl

/-- Each coefficient after layer `j + 1` of `NTT`, whose `len` is `128 >>> j`. -/
theorem nttL_succ_get (f : Poly) {j : Nat} (hj : j < 7) {i : Nat} (hi : i < 256) :
    (nttL (j + 1) f)[i]! =
      if i % (2 * (128 >>> j)) < 128 >>> j then
        (nttL j f)[i]! + zeta (128 / (128 >>> j) + i / (2 * (128 >>> j))) * (nttL j f)[i + (128 >>> j)]!
      else (nttL j f)[i - (128 >>> j)]! -
        zeta (128 / (128 >>> j) + i / (2 * (128 >>> j))) * (nttL j f)[i]! := by
  rw [nttL_succ f hj]
  exact nttLayer_get _ (by match j, hj with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide)
    (by match j, hj with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide) hi

/-- Each coefficient after layer `j + 1` of `NTT⁻¹`, whose `len` is `2 <<< j`. -/
theorem nttInvL_succ_get (f : Poly) {j : Nat} (hj : j < 7) {i : Nat} (hi : i < 256) :
    (nttInvL (j + 1) f)[i]! =
      if i % (2 * (2 <<< j)) < 2 <<< j then (nttInvL j f)[i]! + (nttInvL j f)[i + (2 <<< j)]!
      else zeta (256 / (2 <<< j) - 1 - i / (2 * (2 <<< j))) *
        ((nttInvL j f)[i]! - (nttInvL j f)[i - (2 <<< j)]!) := by
  rw [nttInvL_succ f hj]
  exact nttInvLayer_get _ (by match j, hj with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide)
    (by match j, hj with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide) hi

end VG.Proof.MlKem
