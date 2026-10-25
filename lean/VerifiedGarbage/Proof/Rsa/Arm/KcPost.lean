module
public import VerifiedGarbage.Proof.Rsa.Arm.KcBody
public import VerifiedGarbage.Proof.Rsa.Arm.KcLoads

import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Rsa.Octets

/-! # The checks of an RSA key on ARMv7: the result is `checkCrtKey`, or `checkKey`

`crtP`, `keyP`: what the checks say of their mask (from `CrtOut`,
`KeyOut`), and `crt_result`, `key_result`: with a valid modulus and
exponent, that mask is `crtKeyValid`, or `keyValid`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- What `crtBody` says of its mask. -/
def crtP (g : Geo) (v : Vals) (c : Bool) : Prop := ∃ X₁ X₂ R₁ R₂ R₃,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧ ProdsOk g v R₁ R₂ R₃ ∧
  c = VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃

/-- What `keyBody` says of its mask. -/
def keyP (g : Geo) (v : Vals) (c : Bool) : Prop := ∃ X₁ X₂ R₁ R₂ R₃ Y₁ Y₂,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧ ProdsOk g v R₁ R₂ R₃ ∧
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧ (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2))) ∧
  c = VG.Proof.Rsa.keyBits' v.n v.d v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃ Y₁ Y₂

theorem crtBody_post {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa crtBody s fun t => ∃ A live c, Stg g s A live c t ∧ crtP g v c :=
  WP.mono (crtBody_ok h) fun _ ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, ht⟩ => ⟨_, _, _, ht, X₁, X₂, R₁, R₂, R₃, hX, hR, rfl⟩

theorem keyBody_post {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa keyBody s fun t => ∃ A live c, Stg g s A live c t ∧ keyP g v c :=
  WP.mono (keyBody_ok h) fun _ ⟨X₁, X₂, R₁, R₂, R₃, Y₁, Y₂, hX, hR, hY₁, hY₂, A, live, ht⟩ =>
    ⟨A, live, _, ht, X₁, X₂, R₁, R₂, R₃, Y₁, Y₂, hX, hR, hY₁, hY₂, rfl⟩

/-- The products, for `e` below `2^33` and `p`, `q` shorter than `n`. -/
theorem prods {g : Geo} {v : Vals} {R₁ R₂ R₃ : Nat} (h : ProdsOk g v R₁ R₂ R₃) (he : v.e < 2 ^ 33)
    (hp : 2 * v.p ≤ 2 ^ (32 * g.w)) (hq : v.q < 2 ^ (32 * g.w)) (hq2 : 2 * v.q ≤ 2 ^ (32 * g.w)) :
    (v.dP < 2 * (v.p / 2) → R₁ = v.e * v.dP % (2 * (v.p / 2))) ∧
    (v.dQ < 2 * (v.q / 2) → R₂ = v.e * v.dQ % (2 * (v.q / 2))) ∧
    (v.qI < v.p → R₃ = v.q * v.qI % v.p) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_⟩
  · rw [h1 l (by omega_arith), Nat.mod_eq_of_lt he]
  · rw [h2 l (by omega_arith), Nat.mod_eq_of_lt he]
  · rw [h3 l hp, Nat.mod_eq_of_lt hq]

theorem pow_len {k K w : Nat} (hk : k < K) (hw : K ≤ 4 * w) : 2 * 256 ^ k ≤ 2 ^ (32 * w) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, ← Nat.pow_succ']
  exact Nat.pow_le_pow_right (by decide) (by omega_arith)

theorem pow_len' {k K : Nat} (hk : k ≤ K - 1) : 256 ^ k ≤ 256 ^ (K - 1) :=
  Nat.pow_le_pow_right (by decide) hk

/-- `checkCrtKey` from the mask of `crtBody`. -/
theorem crt_result {g : Geo} {nb eb pb qb dPb dQb qIb : List Byte} {c : Bool}
    (hK : nb.length = g.K) (hK0 : 0 < g.K) (hp : pb.length < g.K) (hq : qb.length < g.K)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) g.K = true → Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true →
      crtP g ⟨Spec.Rsa.os2ip nb, Spec.Rsa.os2ip eb, Spec.Rsa.os2ip pb, Spec.Rsa.os2ip qb, Spec.Rsa.os2ip dPb,
        Spec.Rsa.os2ip dQb, Spec.Rsa.os2ip qIb, 0⟩ c) :
    (if Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) g.K && Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) && c
      then 1 else 0) = if Spec.Rsa.checkCrtKey nb eb pb qb dPb dQb qIb then 1 else 0 := by
  unfold Spec.Rsa.checkCrtKey
  rw [hK]
  by_cases hme : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) g.K = true ∧
      Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true
  · obtain ⟨hm, he⟩ := hme
    obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, rfl⟩ := hc hm he
    have he' := he
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he'
    have lp := VG.Proof.Rsa.lt_of_os2ip pb
    have lq := VG.Proof.Rsa.lt_of_os2ip qb
    have hw : g.K ≤ 4 * g.w := by simp only [Geo.w]; omega_arith
    have pp := pow_len hp hw
    have pq := pow_len hq hw
    have p1 : 256 ^ pb.length ≤ 256 ^ (g.K - 1) := pow_len' (by omega_arith)
    have q1 : 256 ^ qb.length ≤ 256 ^ (g.K - 1) := pow_len' (by omega_arith)
    obtain ⟨h1, h2, h3⟩ := prods hR he'.2 (by show 2 * Spec.Rsa.os2ip pb ≤ _; omega_arith)
      (by show Spec.Rsa.os2ip qb < _; omega_arith) (by show 2 * Spec.Rsa.os2ip qb ≤ _; omega_arith)
    rw [VG.Proof.Rsa.crtKeyValid_bits hm he (Nat.lt_of_lt_of_le lp p1) (Nat.lt_of_lt_of_le lq q1) (fun pos => ⟨(hX pos).2, (hX pos).1⟩) h1 h2 h3, hm, he]
    rfl
  · have : (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) g.K && Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)) = false := by
      simpa [Bool.and_eq_true] using hme
    have hv : Spec.Rsa.crtKeyValid g.K (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dPb) (Spec.Rsa.os2ip dQb) (Spec.Rsa.os2ip qIb) = false := by
      unfold Spec.Rsa.crtKeyValid
      simp only [this, Bool.false_and]
    rw [this, hv]
    rfl

/-- `checkKey` from the mask of `keyBody`. -/
theorem key_result {g : Geo} {nb eb db pb qb dPb dQb qIb : List Byte} {c : Bool}
    (hK : nb.length = g.K) (hK0 : 0 < g.K) (hp : pb.length < g.K) (hq : qb.length < g.K)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) g.K = true → Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true →
      keyP g ⟨Spec.Rsa.os2ip nb, Spec.Rsa.os2ip eb, Spec.Rsa.os2ip pb, Spec.Rsa.os2ip qb, Spec.Rsa.os2ip dPb,
        Spec.Rsa.os2ip dQb, Spec.Rsa.os2ip qIb, Spec.Rsa.os2ip db⟩ c) :
    (if Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) g.K && Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) && c
      then 1 else 0) = if Spec.Rsa.checkKey nb eb db pb qb dPb dQb qIb then 1 else 0 := by
  unfold Spec.Rsa.checkKey
  rw [hK]
  by_cases hme : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) g.K = true ∧
      Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true
  · obtain ⟨hm, he⟩ := hme
    obtain ⟨X₁, X₂, R₁, R₂, R₃, Y₁, Y₂, hX, hR, hY₁, hY₂, rfl⟩ := hc hm he
    have he' := he
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he'
    have lp := VG.Proof.Rsa.lt_of_os2ip pb
    have lq := VG.Proof.Rsa.lt_of_os2ip qb
    have hw : g.K ≤ 4 * g.w := by simp only [Geo.w]; omega_arith
    have pp := pow_len hp hw
    have pq := pow_len hq hw
    have p1 : 256 ^ pb.length ≤ 256 ^ (g.K - 1) := pow_len' (by omega_arith)
    have q1 : 256 ^ qb.length ≤ 256 ^ (g.K - 1) := pow_len' (by omega_arith)
    obtain ⟨h1, h2, h3⟩ := prods hR he'.2 (by show 2 * Spec.Rsa.os2ip pb ≤ _; omega_arith)
      (by show Spec.Rsa.os2ip qb < _; omega_arith) (by show 2 * Spec.Rsa.os2ip qb ≤ _; omega_arith)
    rw [VG.Proof.Rsa.keyValid_bits hm he (Nat.lt_of_lt_of_le lp p1) (Nat.lt_of_lt_of_le lq q1) (fun pos => ⟨(hX pos).2, (hX pos).1⟩) h1 h2 h3 hY₁ hY₂, hm, he]
    rfl
  · have : (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) g.K && Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)) = false := by
      simpa [Bool.and_eq_true] using hme
    have hv : Spec.Rsa.keyValid g.K (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip db)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dPb) (Spec.Rsa.os2ip dQb)
        (Spec.Rsa.os2ip qIb) = false := by
      unfold Spec.Rsa.keyValid
      simp only [this, Bool.false_and]
    rw [this, hv]
    rfl

theorem vals_lt {v : Vals} {P : Nat} (h0 : 0 < P) (hn : v.n < P) (he : v.e < P) (hp : v.p < P)
    (hq : v.q < P) (hdP : v.dP < P) (hdQ : v.dQ < P) (hqI : v.qI < P) (hd : v.d < P) : ∀ j, vals v j < P := by
  intro j
  simp only [vals, upd]
  repeat' split
  all_goals assumption

/-- A number of at most `K` bytes, in `w` words. -/
theorem os2ip_lt_words {bs : List Byte} {w : Nat} (h : bs.length ≤ 4 * w) :
    Spec.Rsa.os2ip bs < 2 ^ (32 * w) :=
  Nat.lt_of_lt_of_le (VG.Proof.Rsa.lt_of_os2ip bs)
    (by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega_arith))

theorem bytesV_lt {σ : State} {src : BitVec 32} {k w : Nat} (h : k ≤ 4 * w) : bytesV σ src k < 2 ^ (32 * w) :=
  os2ip_lt_words (by rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; exact h)

end VG.Proof.Rsa.Arm.KeyCheck
