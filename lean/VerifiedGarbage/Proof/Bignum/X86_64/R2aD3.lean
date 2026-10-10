import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep

/-!
# `R² mod m` by word steps with ADX: Knuth's test with the second words

`R2Adx.refine` (`Impl/Bignum/X86_64/R2Adx.lean`) lowers `q̂` by one when
`r̂ = u₂ 2^64 + u₁ - q̂ d < 2^64` and `q̂ d₁ > r̂ 2^64 + u₀` (TAOCP vol. 2,
§4.3.1, Algorithm D, step D3): `d3`. Then `q̂` was more than the quotient
(`d3_ge`), so it stays at least the quotient, and at most what it was
(`d3_le`), and `R2Words.quot`'s estimate refined twice is within
`q ≤ q̂ ≤ q + 2` (`d3_bounds`); `wordStep_valG` is `WordStep.wordStep_val`
for any such estimate. `refine_ok` is the code's test.
-/

namespace VG.Proof.Bignum.X86_64.R2ax

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.WordStep
open VG.Proof.Bignum.X86_64.R2w (addrm16)

/-- Step D3's test, with `u₂ 2^64 + u₁ ≥ q̂ d`. -/
def d3 (q u2 u1 u0 d d1 : Nat) : Nat :=
  if u2 * 2 ^ 64 + u1 - q * d < 2 ^ 64 ∧ (u2 * 2 ^ 64 + u1 - q * d) * 2 ^ 64 + u0 < q * d1 then q - 1 else q

theorem d3_le (q u2 u1 u0 d d1 : Nat) : d3 q u2 u1 u0 d d1 ≤ q := by
  unfold d3
  by_cases hc : u2 * 2 ^ 64 + u1 - q * d < 2 ^ 64 ∧ (u2 * 2 ^ 64 + u1 - q * d) * 2 ^ 64 + u0 < q * d1
  · simp only [hc, and_self, ↓reduceIte]; omega
  · simp only [hc, ↓reduceIte]; exact Nat.le_refl _

/-- The test keeps `q̂ d ≤ u₂ 2^64 + u₁`. -/
theorem d3_mul_le {q u2 u1 u0 d d1 : Nat} (h : q * d ≤ u2 * 2 ^ 64 + u1) :
    d3 q u2 u1 u0 d d1 * d ≤ u2 * 2 ^ 64 + u1 :=
  Nat.le_trans (Nat.mul_le_mul_right d (d3_le ..)) h

/-- The test keeps `q̂` at least the quotient `q` of `y = T B + yₗ` by
`m = (d 2^64 + d₁) B + mₗ` (`T = (u₂ 2^64 + u₁) 2^64 + u₀`, `yₗ < B`). -/
theorem d3_ge {q qh u2 u1 u0 d d1 yl ml B y m : Nat} (hyl : yl < B)
    (hy : y = ((u2 * 2 ^ 64 + u1) * 2 ^ 64 + u0) * B + yl) (hm : m = (d * 2 ^ 64 + d1) * B + ml)
    (hq : q * m ≤ y) (hqh : q ≤ qh) (hd : qh * d ≤ u2 * 2 ^ 64 + u1) : q ≤ d3 qh u2 u1 u0 d d1 := by
  unfold d3
  by_cases hc : u2 * 2 ^ 64 + u1 - qh * d < 2 ^ 64 ∧ (u2 * 2 ^ 64 + u1 - qh * d) * 2 ^ 64 + u0 < qh * d1
  · simp only [hc, and_self, ↓reduceIte]
    obtain ⟨-, hc⟩ := hc
    generalize 2 ^ 64 = K at *
    -- `q (d K + d₁) ≤ T < q̂ (d K + d₁)`.
    generalize hT : (u2 * K + u1) * K + u0 = T at hy
    generalize hD : d * K + d1 = D at hm
    have h1 : q * D * B < (T + 1) * B := by
      have : q * D * B ≤ q * m := by rw [hm, Nat.mul_assoc, Nat.mul_add]; exact Nat.le_add_right _ _
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 : q * D ≤ T := Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right h1)
    have h3 : T < qh * D := by
      rw [← hT, ← hD, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm qh d]
      have e : (u2 * K + u1 - qh * d) * K = (u2 * K + u1) * K - d * qh * K := by
        rw [Nat.sub_mul, Nat.mul_comm qh d]
      have : d * qh * K ≤ (u2 * K + u1) * K := by
        rw [Nat.mul_comm d qh]; exact Nat.mul_le_mul_right _ hd
      omega
    have : q < qh := by
      by_contra hc'
      have := Nat.mul_le_mul_right D (show qh ≤ q by omega)
      omega
    omega
  · simp only [hc, ↓reduceIte]; exact hqh

/-- `WordStep.wordStep_val` for any estimate `q ≤ q̂ ≤ q + 2` of the quotient
`q = ⌊x 2^64 / m⌋`, for `m < 2^(64 w)`. -/
theorem wordStep_valG {w X M qh T1 T2 T3 b c1 c2 : Nat} (hM0 : 0 < M) (hMw : M < 2 ^ (64 * w))
    (hge : X * 2 ^ 64 / M ≤ qh) (hle : qh ≤ X * 2 ^ 64 / M + 2)
    (hT1 : T1 < 2 ^ (64 * (w + 1))) (hb : b < 2)
    (h1 : T1 + qh * M = X * 2 ^ 64 + 2 ^ (64 * (w + 1)) * b)
    (hT2 : T2 < 2 ^ (64 * (w + 1))) (hc1 : c1 < 2)
    (h2 : T2 + 2 ^ (64 * (w + 1)) * c1 = T1 + if 2 ^ (64 * (w + 1)) / 2 ≤ T1 then M else 0)
    (hT3 : T3 < 2 ^ (64 * (w + 1))) (hc2 : c2 < 2)
    (h3 : T3 + 2 ^ (64 * (w + 1)) * c2 = T2 + if 2 ^ (64 * (w + 1)) / 2 ≤ T2 then M else 0) :
    T3 = X * 2 ^ 64 % M := by
  have hWB : 2 ^ (64 * (w + 1)) = 2 ^ (64 * w) * 2 ^ 64 := by
    rw [show 64 * (w + 1) = 64 * w + 64 by omega, Nat.pow_add]
  generalize hW : 2 ^ (64 * (w + 1)) = W at *
  generalize 2 ^ (64 * w) = B at *
  have hMW : 4 * M < W / 2 := by rw [hWB]; omega_using [hMw]
  obtain ⟨hfin, hv1, hv2, hw1, hw2⟩ := addBack_two (W := W) hM0 hMW hge hle
  have e1 := twos_of_sub hT1 hb (by omega_using [h1]) hv1 hv2
  have e2 := twos_of_add hv1 hv2 hw1 hw2 e1 hT2 hc1 h2
  have hv1' : -((W : Int) / 2) ≤ addIfNeg M (addIfNeg M ((X * 2 ^ 64 : Nat) - (qh * M : Nat))) := by
    rw [hfin]; omega_using []
  have hv2' : addIfNeg M (addIfNeg M ((X * 2 ^ 64 : Nat) - (qh * M : Nat))) < (W : Int) / 2 := by
    rw [hfin]; have := Nat.mod_lt (X * 2 ^ 64) hM0; omega_using [hMW, this]
  have e3 := twos_of_add hw1 hw2 hv1' hv2' e2 hT3 hc2 h3
  rw [e3, hfin]
  have hr := Nat.mod_lt (X * 2 ^ 64) hM0
  have hMW' : M < W := Nat.lt_of_lt_of_le (by omega_using [hMW]) (Nat.div_le_self W 2)
  unfold twos
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_trans hr hMW')), Int.toNat_natCast]

/-- The estimate refined twice: `q ≤ q̂ ≤ q + 2` for the quotient `q` of
`x 2^64` by `m`, for `x < m`, `m`'s top word `d ≥ 2^63`. -/
theorem d3_bounds {X M U2 U1 U0 D D1 Xl Ml B0 : Nat}
    (hX : X = ((U2 * 2 ^ 64 + U1) * 2 ^ 64 + U0) * B0 + Xl) (hXl : Xl < B0)
    (hM : M = (D * 2 ^ 64 + D1) * 2 ^ 64 * B0 + Ml) (hMl : Ml < 2 ^ 64 * B0)
    (hU0 : U0 < 2 ^ 64) (hD1 : D1 < 2 ^ 64) (hd : 2 ^ 63 ≤ D) (hXM : X < M) :
    X * 2 ^ 64 / M ≤ d3 (d3 (min ((U2 * 2 ^ 64 + U1) / D) (2 ^ 64 - 1)) U2 U1 U0 D D1) U2 U1 U0 D D1 ∧
      d3 (d3 (min ((U2 * 2 ^ 64 + U1) / D) (2 ^ 64 - 1)) U2 U1 U0 D D1) U2 U1 U0 D D1 ≤ X * 2 ^ 64 / M + 2 ∧
      d3 (d3 (min ((U2 * 2 ^ 64 + U1) / D) (2 ^ 64 - 1)) U2 U1 U0 D D1) U2 U1 U0 D D1 < 2 ^ 64 := by
  generalize hK : 2 ^ 64 = K at *
  have hK0 : 0 < K := by rw [← hK]; exact Nat.two_pow_pos 64
  have hM0 : 0 < M := by omega
  -- `y = x K` over `B' = K B₀` and over `B = K K B₀`.
  have hy1 : X * K = ((U2 * K + U1) * K + U0) * (K * B0) + Xl * K := by rw [hX]; grind
  have hyl1 : Xl * K < K * B0 := by rw [Nat.mul_comm Xl]; exact Nat.mul_lt_mul_of_pos_left hXl hK0
  have hm1 : M = (D * K + D1) * (K * B0) + Ml := by rw [hM, Nat.mul_assoc]
  have hy2 : X * K = (U2 * K + U1) * (K * K * B0) + (U0 * B0 + Xl) * K := by rw [hX]; grind
  have hyl2 : (U0 * B0 + Xl) * K < K * K * B0 := by
    have : U0 * B0 + Xl < K * B0 := by
      have := Nat.mul_le_mul_right B0 (show U0 + 1 ≤ K by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    rw [Nat.mul_comm _ (K), Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_left this hK0
  have hm2 : M = D * (K * K * B0) + (D1 * (K * B0) + Ml) := by rw [hM]; grind
  have hml2 : D1 * (K * B0) + Ml < K * K * B0 := by
    have : D1 * (K * B0) + K * B0 ≤ K * K * B0 := by
      have := Nat.mul_le_mul_right (K * B0) (show D1 + 1 ≤ K by omega)
      rwa [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc (K) (K) B0] at this
    omega
  -- `q < K`.
  have hq : X * K / M < K := by
    rw [Nat.div_lt_iff_lt_mul hM0, Nat.mul_comm (K) M]; exact Nat.mul_lt_mul_of_pos_right hXM hK0
  have hq2 := hq
  rw [hy2, hm2] at hq2
  have hge := qhat_ge (N := U2 * K + U1) (d := D) hyl2 (by omega) (by rw [hK]; exact hq2)
  have hle := qhat_le (N := U2 * K + U1) (yl := (U0 * B0 + Xl) * K) hml2 hd (by rw [hK]; exact hq2)
  rw [← hy2, ← hm2, hK] at hge hle
  generalize hqh : min ((U2 * K + U1) / D) (K - 1) = qh at hge hle ⊢
  have hqK : qh < K := by omega
  have hd0 : qh * D ≤ U2 * K + U1 := by
    rw [← hqh]
    exact Nat.le_trans (Nat.mul_le_mul_right D (Nat.min_le_left _ _)) (Nat.div_mul_le_self _ _)
  have hqm : X * K / M * M ≤ X * K := Nat.div_mul_le_self _ _
  subst hK
  have g1 := d3_ge hyl1 hy1 hm1 hqm hge hd0
  have g2 := d3_ge hyl1 hy1 hm1 hqm g1 (d3_mul_le hd0)
  have l2 := Nat.le_trans (d3_le (d3 qh U2 U1 U0 D D1) U2 U1 U0 D D1) (d3_le qh U2 U1 U0 D D1)
  exact ⟨g2, Nat.le_trans l2 hle, Nat.lt_of_le_of_lt l2 hqK⟩

/-- A value of `w ≥ 3` words by its top three. -/
theorem wv_top3 (m : Mem) (B : Addr) (e w : Nat) (hw : 3 ≤ w) :
    wv m B e w = (((word m B (e + 8 * (w - 1))).toNat * 2 ^ 64 + (word m B (e + 8 * (w - 2))).toNat) * 2 ^ 64 +
      (word m B (e + 8 * (w - 3))).toNat) * 2 ^ (64 * (w - 3)) + wv m B e (w - 3) := by
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 3 := ⟨w - 3, by omega⟩
  rw [show n + 3 = n + 1 + 1 + 1 from rfl, wv_succ, wv_succ, wv_succ, show n + 1 + 1 + 1 - 1 = n + 1 + 1 by omega,
    show n + 1 + 1 + 1 - 2 = n + 1 by omega, show n + 1 + 1 + 1 - 3 = n by omega,
    show 64 * (n + 1 + 1) = 64 * n + 64 + 64 by omega, show 64 * (n + 1) = 64 * n + 64 by omega]
  simp only [Nat.pow_add]
  generalize 2 ^ (64 * n) = P
  generalize 2 ^ 64 = K
  grind

/-- A value of `w ≥ 3` words by its top two. -/
theorem wv_top2 (m : Mem) (B : Addr) (e w : Nat) (hw : 3 ≤ w) :
    wv m B e w = ((word m B (e + 8 * (w - 1))).toNat * 2 ^ 64 + (word m B (e + 8 * (w - 2))).toNat) * 2 ^ 64 *
      2 ^ (64 * (w - 3)) + wv m B e (w - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 3 := ⟨w - 3, by omega⟩
  rw [show n + 3 = n + 1 + 1 + 1 from rfl, wv_succ, wv_succ, show n + 1 + 1 + 1 - 1 = n + 1 + 1 by omega,
    show n + 1 + 1 + 1 - 2 = n + 1 by omega, show n + 1 + 1 + 1 - 3 = n by omega,
    show 64 * (n + 1 + 1) = 64 * n + 64 + 64 by omega, show 64 * (n + 1) = 64 * n + 64 by omega]
  simp only [Nat.pow_add]
  generalize 2 ^ (64 * n) = P
  generalize 2 ^ 64 = K
  grind

theorem pow_w2 (w : Nat) (hw : 3 ≤ w) : 2 ^ (64 * (w - 2)) = 2 ^ 64 * 2 ^ (64 * (w - 3)) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- `b + 8 i - 24` for `i = j ≥ 3`. -/
theorem addrm24 {b i p : Addr} {e j : Nat} (hb : b = off p e) (hi : i = BitVec.ofNat 64 j) (hj : 3 ≤ j) :
    b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-24) = off p (e + 8 * (j - 3)) := by
  have h8 : BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 (-24) = BitVec.ofNat 64 (8 * (j - 3)) := by
    rw [show (-24 : Int) = - ((24 : Nat) : Int) by rfl, BitVec.ofInt_neg, BitVec.ofInt_natCast,
      ← BitVec.sub_eq_add_neg, show 8 * j = 8 * (j - 3) + 24 by omega, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  subst hb hi
  rw [ofNat_mul8, off, BitVec.add_assoc, BitVec.add_assoc, h8, ← BitVec.ofNat_add]

/-- The words of `refine`: `q̂ + (-1 if r̂ < 2^64 and its test holds)` is `d3`. -/
theorem refine_arith {qh : Nat} {U2 U1 U0 D D1 lo hi lo2 hi2 : BitVec 64} (hq : qh < 2 ^ 64)
    (e2 : lo.toNat + 2 ^ 64 * hi.toNat = qh * D.toNat) (e4 : lo2.toNat + 2 ^ 64 * hi2.toNat = qh * D1.toNat)
    (hle : qh * D.toNat ≤ U2.toNat * 2 ^ 64 + U1.toNat) :
    BitVec.ofNat 64 qh + (if (U2 - hi - (BitVec.ofBool (decide (U1.toNat < lo.toNat))).setWidth 64 == 0) = true then
      0#64 - (BitVec.ofBool (decide ((U1 - lo).toNat < hi2.toNat + (decide (U0.toNat < lo2.toNat)).toNat))).setWidth 64
      else 0#64) = BitVec.ofNat 64 (d3 qh U2.toNat U1.toNat U0.toNat D.toNat D1.toNat) := by
  unfold d3
  have hU2 := U2.isLt; have hU1 := U1.isLt; have hU0 := U0.isLt; have hlo := lo.isLt; have hhi := hi.isLt
  have hlo2 := lo2.isLt; have hhi2 := hi2.isLt
  generalize qh * D.toNat = P at e2 hle
  have hq0 : qh = 0 → qh * D1.toNat = 0 := fun h => by rw [h, Nat.zero_mul]
  generalize qh * D1.toNat = P1 at e4 hq0
  have h9 : (U1 - lo).toNat = (U1.toNat + 2 ^ 64 - lo.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; omega
  have h11 : (U2 - hi - (BitVec.ofBool (decide (U1.toNat < lo.toNat))).setWidth 64).toNat =
      (U2.toNat * 2 ^ 64 + U1.toNat - P) / 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
    by_cases h : U1.toNat < lo.toNat <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega
  apply BitVec.eq_of_toNat_eq
  by_cases hr : U2.toNat * 2 ^ 64 + U1.toNat - P < 2 ^ 64
  · have hz : (U2 - hi - (BitVec.ofBool (decide (U1.toNat < lo.toNat))).setWidth 64 == 0) = true := by
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [h11]; exact Nat.div_eq_of_lt hr
    have hc : decide ((U1 - lo).toNat < hi2.toNat + (decide (U0.toNat < lo2.toNat)).toNat) =
        decide ((U2.toNat * 2 ^ 64 + U1.toNat - P) * 2 ^ 64 + U0.toNat < P1) := by
      have hr9 : (U1 - lo).toNat = U2.toNat * 2 ^ 64 + U1.toNat - P := by rw [h9]; omega
      rw [hr9]
      generalize U2.toNat * 2 ^ 64 + U1.toNat - P = r at hr ⊢
      by_cases h : U0.toNat < lo2.toNat <;> simp only [h, decide_true, decide_false, Bool.toNat_true,
        Bool.toNat_false] <;> apply decide_eq_decide.mpr <;> omega
    simp only [hz, ↓reduceIte, hc, hr, true_and]
    by_cases h : (U2.toNat * 2 ^ 64 + U1.toNat - P) * 2 ^ 64 + U0.toNat < P1
    · have : qh ≠ 0 := fun h0 => by have := hq0 h0; omega
      simp only [h, decide_true, ↓reduceIte]
      rw [show 0#64 - (BitVec.ofBool true).setWidth 64 = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl, BitVec.toNat_add,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    · simp only [h, decide_false, ↓reduceIte]
      rw [show 0#64 - (BitVec.ofBool false).setWidth 64 = 0#64 from rfl, BitVec.add_zero]
  · have hz : (U2 - hi - (BitVec.ofBool (decide (U1.toNat < lo.toNat))).setWidth 64 == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h; rw [h11] at this; change _ = 0 at this
      omega
    simp only [hz, Bool.false_eq_true, ↓reduceIte, hr, false_and]
    rw [BitVec.add_zero]

/-- `refine`: `q̂ := d3 q̂ …` for the top words of `x` and `m`. -/
theorem refine_ok {t : State} {B : Addr} {Z w ex em qh : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 qh) (hw : 3 ≤ w) (hX : ex + 8 * w ≤ Z) (hM : em + 8 * w ≤ Z)
    (hq : qh < 2 ^ 64)
    (hle : qh * (word t.mem B (em + 8 * (w - 1))).toNat ≤
      (word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (ex + 8 * (w - 2))).toNat) :
    WP isa (.block refine) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 (d3 qh (word t.mem B (ex + 8 * (w - 1))).toNat
        (word t.mem B (ex + 8 * (w - 2))).toNat (word t.mem B (ex + 8 * (w - 3))).toNat
        (word t.mem B (em + 8 * (w - 1))).toNat (word t.mem B (em + 8 * (w - 2))).toNat) ∧ t'.mem = t.mem ∧
      Keep [.rdx, .rax, .r13, .r9, .r11, .r14, .r15, .rcx] t t' := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [.rdx, .rax, .r13, .r9, .r11, .r14, .r15, .rcx] (Q := fun t' =>
      t'.gpr .rcx = BitVec.ofNat 64 (d3 qh (word t.mem B (ex + 8 * (w - 1))).toNat
        (word t.mem B (ex + 8 * (w - 2))).toNat (word t.mem B (ex + 8 * (w - 3))).toNat
        (word t.mem B (em + 8 * (w - 1))).toNat (word t.mem B (em + 8 * (w - 2))).toNat) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  -- The words.
  generalize hu2 : word t.mem B (ex + 8 * (w - 1)) = U2 at hle ⊢
  generalize hu1 : word t.mem B (ex + 8 * (w - 2)) = U1 at hle ⊢
  generalize hu0 : word t.mem B (ex + 8 * (w - 3)) = U0
  generalize hd : word t.mem B (em + 8 * (w - 1)) = D at hle ⊢
  generalize hd1 : word t.mem B (em + 8 * (w - 2)) = D1
  have ea1 : t.ea (ix .r10 .r12 (-8)) = off B (em + 8 * (w - 1)) := by
    simp only [State.ea, ix, h10, h12]; exact addrm8 rfl rfl (by omega)
  rw [show refine = ([.mov .rdx (.reg .rcx)] : List Instr) ++ (([.mulx .rax .r13 (.mem (ix .r10 .r12 (-8)))] : List Instr) ++
    (([.mov .r9 (.mem (ix .rbx .r12 (-16))), .mov .r11 (.mem (ix .rbx .r12 (-8))), .alu .sub .r9 (.reg .r13),
      .alu .sbb .r11 (.reg .rax)] : List Instr) ++ (([.mulx .rax .r13 (.mem (ix .r10 .r12 (-16)))] : List Instr) ++
      (([.mov .r14 (.mem (ix .rbx .r12 (-24))), .alu .sub .r14 (.reg .r13), .alu .sbb .r9 (.reg .rax),
        .alu .sbb .r15 (.reg .r15), .mov32 .r13 (.imm 0), .alu .test .r11 (.reg .r11)] : List Instr) ++
        (([.cmov .ne .r15 (.reg .r13)] : List Instr) ++ ([.alu .add .rcx (.reg .r15)] : List Instr)))))) from rfl,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t₁ => t₁.gpr .rdx = BitVec.ofNat 64 qh ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧
    t₁.wr = t.wr) (by xrun [hcx]) rfl) fun t₁ ⟨⟨h1dx, hm₁, hrd₁, hwr₁⟩, k₁⟩ => ?_
  have hs₁ : Scr t₁ B Z := hs.congr hwr₁
  have r₁ : ∀ r, r ≠ .rdx → t₁.gpr r = t.gpr r := fun r hr => k₁.gpr (by simpa using hr)
  rw [WP.block_append_iff]
  have ea₁ : t₁.ea (ix .r10 .r12 (-8)) = off B (em + 8 * (w - 1)) := by
    simp only [State.ea, ix, r₁ .r10 (by decide), r₁ .r12 (by decide)]
    exact addrm8 h10 h12 (by omega)
  refine WP.mono (mulx_ok t₁ (readSrc_word hs₁ ea₁ (by omega)) (fun _ h => nomatch h) (by decide))
    fun t₂ ⟨e₂, _, _, k₂⟩ => ?_
  rw [h1dx, hm₁, hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq] at e₂
  have r₂ : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .rdx → t₂.gpr r = t.gpr r := fun r h1 h2 h3 =>
    (k₂.gpr (by simp [h1, h2])).trans (r₁ r h3)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r9, .r11] (Q := fun t₃ => t₃.gpr .r9 = U1 - t₂.gpr .r13 ∧
      t₃.gpr .r11 = U2 - t₂.gpr .rax - (BitVec.ofBool (decide (U1.toNat < (t₂.gpr .r13).toNat))).setWidth 64 ∧
      t₃.mem = t.mem ∧ t₃.rd = t.rd ∧ t₃.wr = t.wr) (by
    xrun [State.ea, ix, r₂ .rbx (by decide) (by decide) (by decide), r₂ .r12 (by decide) (by decide) (by decide),
      hbx, h12, addrm8 (p := B) (e := ex) (j := w) rfl rfl (by omega),
      addrm16 (p := B) (e := ex) (j := w) rfl rfl (by omega), k₂.2.1, k₂.2.2.1, k₂.2.2.2, hm₁, hrd₁, hwr₁,
      hs.ld (show ex + 8 * (w - 1) + 8 ≤ Z by omega), hs.ld (show ex + 8 * (w - 2) + 8 ≤ Z by omega), hu1, hu2])
    rfl) fun t₃ ⟨⟨h9, h11, hm₃, hrd₃, hwr₃⟩, k₃⟩ => ?_
  have hs₃ : Scr t₃ B Z := hs.congr hwr₃
  have r₃ : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t₃.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 =>
    (k₃.gpr (by simp [h4, h5])).trans (r₂ r h1 h2 h3)
  have ea₃ : t₃.ea (ix .r10 .r12 (-16)) = off B (em + 8 * (w - 2)) := by
    simp only [State.ea, ix, r₃ .r10 (by decide) (by decide) (by decide) (by decide) (by decide),
      r₃ .r12 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact addrm16 h10 h12 (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok t₃ (readSrc_word hs₃ ea₃ (by omega)) (fun _ h => nomatch h) (by decide))
    fun t₄ ⟨e₄, _, _, k₄⟩ => ?_
  have h4dx : t₄.gpr .rdx = BitVec.ofNat 64 qh := by
    rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), h1dx]
  have h3dx : t₃.gpr .rdx = BitVec.ofNat 64 qh := by rw [k₃.gpr (by decide), k₂.gpr (by decide), h1dx]
  rw [h3dx, hm₃, hd1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq] at e₄
  have r₄ : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t₄.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 =>
    (k₄.gpr (by simp [h1, h2])).trans (r₃ r h1 h2 h3 h4 h5)
  have h9₄ : t₄.gpr .r9 = t₃.gpr .r9 := k₄.gpr (by decide)
  have h11₄ : t₄.gpr .r11 = t₃.gpr .r11 := k₄.gpr (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r14, .r9, .r15, .r13, .r11] (Q := fun t₅ => t₅.gpr .r15 = 0#64 -
      (BitVec.ofBool (decide ((U1 - t₂.gpr .r13).toNat < (t₄.gpr .rax).toNat +
        (decide (U0.toNat < (t₄.gpr .r13).toNat)).toNat))).setWidth 64 ∧ t₅.gpr .r13 = 0 ∧
      t₅.zf = some (t₃.gpr .r11 == 0) ∧ t₅.mem = t.mem) (by
    xrun [State.ea, ix, r₄ .rbx (by decide) (by decide) (by decide) (by decide) (by decide),
      r₄ .r12 (by decide) (by decide) (by decide) (by decide) (by decide), hbx, h12, h9₄, h11₄, h9,
      addrm24 (p := B) (e := ex) (j := w) rfl rfl (by omega), k₄.2.1, k₄.2.2.1, k₄.2.2.2, hm₃, hrd₃, hwr₃,
      hs.ld (show ex + 8 * (w - 3) + 8 ≤ Z by omega), hu0, BitVec.and_self]
) rfl)
    fun t₅ ⟨⟨h515, h513, h5z, hm₅⟩, k₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (R2w.cmovne_ok (d := .r15) (r := .r13) h5z) fun t₆ ⟨h615, hm₆, k₆⟩ => ?_
  have h6cx : t₆.gpr .rcx = BitVec.ofNat 64 qh := by
    rw [k₆.gpr (by decide), k₅.gpr (by decide), r₄ .rcx (by decide) (by decide) (by decide) (by decide)
      (by decide), hcx]
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.gpr .rcx = t₆.gpr .rcx + t₆.gpr .r15 ∧ t'.mem = t₆.mem)
    (by xrun) rfl) fun t' ⟨⟨hcx', hm'⟩, k'⟩ => ⟨?_, hm'.trans (hm₆.trans hm₅)⟩
  rw [hcx', h6cx, h615, h515, h513, h11]
  rw [← hu2, ← hu1, ← hu0, ← hd, ← hd1] at *
  exact refine_arith hq e₂ e₄ hle

end VG.Proof.Bignum.X86_64.R2ax
