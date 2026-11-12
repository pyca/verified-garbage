module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordSub
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.LongDivision

meta import VerifiedGarbage.Proof.Rsa.X86_64.WordSub
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.WordStep
meta import VerifiedGarbage.Proof.Bignum.WordStepNorm
meta import VerifiedGarbage.Proof.Bignum.LongDivision

/-! # A normalized remainder step with a full low input word

The 3-by-2 quotient estimate, multiword multiply-subtract and one masked
correction compute `(remainder * 2^64 + digit) mod modulus` at the factors' width, while
the surrounding workspace may have a different stride.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordReduce

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Bignum.X86_64.R2w
open VG.Proof.Bignum.WordStep

/-- `WordStep.wordStepQ1_val` for the dividend `y`: `t₁ = y - q̂ m` modulo `W > 4 m`
and `m` added once if its top half is set is `y mod m`, for `⌊y / m⌋ ≤ q̂ ≤ ⌊y / m⌋ + 1`. -/
theorem stepQ1_val {W y M qh T1 T2 b c : Nat} (hM0 : 0 < M) (hMW : 2 * M < W / 2)
    (hge : y / M ≤ qh) (hle : qh ≤ y / M + 1)
    (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + qh * M = y + W * b)
    (hT2 : T2 < W) (hc : c < 2) (h2 : T2 + W * c = T1 + if W / 2 ≤ T1 then M else 0) :
    T2 = y % M := by
  obtain ⟨hfin, hv1, hv2⟩ := addBack_one (W := W) hM0 hMW hge hle
  have e1 := twos_of_sub hT1 hb (by omega_using [h1]) hv1 hv2
  have hw1 : -((W : Int) / 2) ≤ addIfNeg M ((y : Nat) - (qh * M : Nat)) := by
    rw [hfin]; omega_using []
  have hw2 : addIfNeg M ((y : Nat) - (qh * M : Nat)) < (W : Int) / 2 := by
    rw [hfin]; have := Nat.mod_lt y hM0; omega_using [hMW, this]
  have e2 := twos_of_add hv1 hv2 hw1 hw2 e1 hT2 hc h2
  rw [e2, hfin]
  have hr := Nat.mod_lt y hM0
  have hMW' : M < W := Nat.lt_of_lt_of_le (by omega_using [hMW]) (Nat.div_le_self W 2)
  unfold twos
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_trans hr hMW')), Int.toNat_natCast]

/-- `step_ok`, with the quotient's digit `⌊(x 2^64 + digit) / m⌋` left as
`rcx + r11`: the estimate `q̂` and the mask of its correction. -/
theorem stepQ_ok {t : State} {B : Addr} {Z w ex em et ev : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h8 : t.gpr .r8 = off B et)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hbp : t.gpr .rbp = off B ev)
    (hw : 3 ≤ w) (hw' : w < 2 ^ 30)
    (hXz : ex + 8 * w ≤ Z) (hMz : em + 8 * w ≤ Z) (hTz : et + 8 * (w + 1) ≤ Z) (hE : ev + 16 ≤ Z)
    (sepX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et)
    (sepM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et)
    (hd : 2 ^ 63 ≤ (word t.mem B (em + 8 * (w - 1))).toNat)
    (hv : (word t.mem B ev).toNat =
      (2 ^ 128 - 1) / (word t.mem B (em + 8 * (w - 1))).toNat - 2 ^ 64)
    (hx : wv t.mem B ex w < wv t.mem B em w) :
    WP isa Impl.Rsa.X86_64.WordReduce.step t fun t' =>
      wv t'.mem B ex w = (wv t.mem B ex w * 2 ^ 64 + (word t.mem B (ev + 8)).toNat) % wv t.mem B em w ∧
      Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t.mem t'.mem ∧ Keep mmRegs t t' ∧
      (t'.gpr .rcx + t'.gpr .r11).toNat =
        (wv t.mem B ex w * 2 ^ 64 + (word t.mem B (ev + 8)).toNat) / wv t.mem B em w := by
  have hn := hs.nowrap
  unfold Impl.Rsa.X86_64.WordReduce.step
  change WP isa (.seq (.block quot) (.seq (.block refine3) (.seq Impl.Rsa.X86_64.WordReduce.mulSub
    (.seq addBack copyBack)))) t _
  generalize hX : wv t.mem B ex w = X at hx
  generalize hM : wv t.mem B em w = M at hx
  have hu := top_le (by omega_arith) (hX ▸ hM ▸ hx)
  have e1 : ex + 8 * w ≤ Z := hXz
  have e2 : em + 8 * w ≤ Z := hMz
  have e3 : ev + 8 ≤ Z := by omega_arith
  have eT : et + 8 * (w + 1) ≤ Z := hTz
  have sX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et := sepX
  have sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et := sepM
  have hw31 : w < 2 ^ 31 := by omega_arith
  have hq := quot_ok hs hbx h10 h12 hbp (by omega_arith) e1 e2 e3 hu hd hv
  refine WP.seq (WP.mono hq fun t₂ ⟨h2cx, hm₂, k₂⟩ => ?_)
  have hs₂ := hs.congr k₂.2.2
  have t₂bx : t₂.gpr .rbx = off B ex := (k₂.gpr (by decide)).trans hbx
  have t₂10 : t₂.gpr .r10 = off B em := (k₂.gpr (by decide)).trans h10
  have t₂8 : t₂.gpr .r8 = off B et := (k₂.gpr (by decide)).trans h8
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h12
  have t₂bp : t₂.gpr .rbp = off B ev := (k₂.gpr (by decide)).trans hbp
  -- The estimates.
  have hX' : X = (word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) +
      (word t.mem B (ex + 8 * (w - 3))).toNat * 2 ^ (64 * (w - 3)) + wv t.mem B ex (w - 3) := by
    rw [← hX, show w = (w - 3) + 1 + 1 + 1 by omega_arith, wv_succ, wv_succ, wv_succ,
      show w - 3 + 1 + 1 + 1 - 1 = w - 3 + 1 + 1 by omega_arith, show w - 3 + 1 + 1 + 1 - 2 = w - 3 + 1 by omega_arith,
      show w - 3 + 1 + 1 + 1 - 3 = w - 3 by omega_arith]
    grind
  have hM' : M = (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (em + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wv t.mem B em (w - 2) := by
    rw [← hM, show w = (w - 2) + 1 + 1 by omega_arith, wv_succ, wv_succ, show w - 2 + 1 + 1 - 1 = w - 2 + 1 by omega_arith,
      show w - 2 + 1 + 1 - 2 = w - 2 by omega_arith]
    grind
  obtain ⟨hUD, hq1, hq2, -, -⟩ := norm3 hw hX' (wv_lt _ _ _ _) hM' (wv_lt _ _ _ _) (BitVec.isLt _) (BitVec.isLt _) hd hx
  have h2cx' := congrArg BitVec.toNat h2cx
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide))] at h2cx'
  have hD0 : 0 < (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat := by
    omega_arith
  have hr := refine3_ok hs₂ t₂bx t₂10 t₂12 hw e1 e2 (by rw [hm₂]) (by rw [hm₂]) hD0 hUD
    (by rw [h2cx']; exact hq1) (by rw [h2cx']; exact hq2)
  refine WP.seq (WP.mono hr fun t₂' ⟨h2'cx, hm₂', k₂'⟩ => ?_)
  have hs₂' := hs₂.congr k₂'.2.2
  have t₂'bx : t₂'.gpr .rbx = off B ex := (k₂'.gpr (by decide)).trans t₂bx
  have t₂'10 : t₂'.gpr .r10 = off B em := (k₂'.gpr (by decide)).trans t₂10
  have t₂'8 : t₂'.gpr .r8 = off B et := (k₂'.gpr (by decide)).trans t₂8
  have t₂'12 : t₂'.gpr .r12 = BitVec.ofNat 64 w := (k₂'.gpr (by decide)).trans t₂12
  have t₂'bp : t₂'.gpr .rbp = off B ev := (k₂'.gpr (by decide)).trans t₂bp
  have hms := mulSub_ok hs₂' t₂'bx t₂'10 t₂'8 t₂'bp hE t₂'12 (by omega_arith) hw31 e1 e2 eT sX sM
  refine WP.seq (WP.mono hms fun t₃ ⟨b, hv₃, ho₃, k₃⟩ => ?_)
  rw [h2'cx] at hv₃
  have hs₃ := hs₂'.congr k₃.2.2
  have t₃10 : t₃.gpr .r10 = off B em := (k₃.gpr (by decide)).trans t₂'10
  have t₃8 : t₃.gpr .r8 = off B et := (k₃.gpr (by decide)).trans t₂'8
  have t₃12 : t₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans t₂'12
  have hab₃ := addBack_ok' hs₃ t₃10 t₃8 t₃12 (by omega_arith) hw31 e2 eT sM
  refine WP.seq (WP.mono hab₃ fun t₅ ⟨c1, hv₅, ho₅, k₅, h11₅⟩ => ?_)
  have hs₅ := hs₃.congr k₅.2.2
  have t₅bx : t₅.gpr .rbx = off B ex :=
    (k₅.gpr (by decide)).trans ((k₃.gpr (by decide)).trans t₂'bx)
  have t₅8 : t₅.gpr .r8 = off B et := (k₅.gpr (by decide)).trans t₃8
  have t₅12 : t₅.gpr .r12 = BitVec.ofNat 64 w := (k₅.gpr (by decide)).trans t₃12
  unfold R2Words.copyBack
  refine WP.seq (WP.mono (WP.keep [.rsi] (Q := fun t' => t'.gpr .rsi = off B et ∧ t'.mem = t₅.mem)
    (by xrun [t₅8]) rfl) fun t₆ ⟨⟨h6si, hm₆⟩, k₆⟩ => ?_)
  have hsepw : ∀ j < w, ∀ b < 8, ofs B (off B (et + 8 * j) + BitVec.ofNat 64 b) < ex ∨
      ex + 8 * w ≤ ofs B (off B (et + 8 * j) + BitVec.ofNat 64 b) := fun j hj b hb => by
    rw [ofs_off B (by omega_arith)]; omega_arith
  have hs₆ := hs₅.congr k₆.2.2
  have hrd : ∀ j < w, InRegions (t₆.rd ++ t₆.wr) (off B (et + 8 * j)) 8 := fun j hj => hs₆.ld (by omega_arith)
  have hwr : ∀ j < w, InRegions t₆.wr (off B (ex + 8 * j)) 8 := fun j hj => hs₆.st (by omega_arith)
  have hcw := copyWords_ok (S := B) (D := B) h6si ((k₆.gpr (by decide)).trans t₅bx)
    ((k₆.gpr (by decide)).trans t₅12) (by omega_arith) hw31 (by omega_arith) hrd hwr hsepw
  refine WP.mono hcw fun t' ⟨hc, _, ho', k'⟩ => ?_
  -- Memory: `m`, `x` and the digit as on entry until the copy.
  have hm₂₂ : t₂'.mem = t.mem := by rw [hm₂', hm₂]
  have em3 : ∀ {d n}, d + 8 * n ≤ et ∨ et + 8 * (w + 1) ≤ d → d + 8 * n ≤ Z →
      wv t₃.mem B d n = wv t.mem B d n := fun h h' => by
    rw [ho₃.wv (by omega_arith) (by omega_arith), hm₂₂]
  rw [em3 (n := w) (d := em) (by omega_arith) (by omega_arith), hM] at hv₅
  rw [hm₂₂, hX, hM] at hv₃
  simp only [← top_half] at hv₅
  -- The quotient's bounds, for the dividend `y = x 2^64 + digit`.
  generalize hg : (word t.mem B (ev + 8)).toNat = g at hv₃
  have hg' : g < 2 ^ 64 := hg ▸ BitVec.isLt _
  have hMw : M < 2 ^ (64 * w) := by rw [← hM]; exact wv_lt _ _ _ _
  have hy : (X * 2 ^ 64 + g) / M < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by omega_arith)]
    have := Nat.mul_le_mul_right (2 ^ 64) (show X + 1 ≤ M by omega_arith)
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm (2 ^ 64)]; omega_arith
  have hK : (X * 2 ^ 64 + g) / 2 ^ (64 * (w - 2)) = X / 2 ^ (64 * (w - 3)) := by
    rw [show 64 * (w - 2) = 64 + 64 * (w - 3) by omega_arith, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      div_pow_cancel hg']
  have e128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := Nat.pow_add 2 64 64
  have hXK : X / 2 ^ (64 * (w - 3)) = (word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 128 +
      (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ 64 + (word t.mem B (ex + 8 * (w - 3))).toNat := by
    have e : X = ((word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 128 +
        (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ 64 + (word t.mem B (ex + 8 * (w - 3))).toNat) *
          2 ^ (64 * (w - 3)) + wv t.mem B ex (w - 3) := by
      rw [hX', show 64 * (w - 1) = 64 * (w - 3) + 64 + 64 by omega_arith,
        show 64 * (w - 2) = 64 * (w - 3) + 64 by omega_arith, Nat.pow_add, Nat.pow_add, e128]
      generalize 2 ^ (64 * (w - 3)) = P; generalize 2 ^ 64 = Bq
      grind
    rw [e, div_pow_cancel (wv_lt _ _ _ _)]
  have hMK : M / 2 ^ (64 * (w - 2)) = (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 +
      (word t.mem B (em + 8 * (w - 2))).toNat := by
    have e : M = ((word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat) *
        2 ^ (64 * (w - 2)) + wv t.mem B em (w - 2) := by
      rw [hM', show 64 * (w - 1) = 64 * (w - 2) + 64 by omega_arith, Nat.pow_add]
      generalize 2 ^ (64 * (w - 2)) = P; generalize 2 ^ 64 = Bq
      grind
    rw [e, div_pow_cancel (wv_lt _ _ _ _)]
  have hD64 : 2 ^ 64 ≤ M / 2 ^ (64 * (w - 2)) := by rw [hMK]; omega_arith
  obtain ⟨hge, hle⟩ := qhat_trunc hy hD64
  rw [hK, hXK, hMK] at hge hle
  have hW : 2 * M < 2 ^ (64 * (w + 1)) / 2 := by
    rw [show 64 * (w + 1) = 64 * w + 64 by omega_arith, Nat.pow_add]
    omega_arith
  have hT3 := stepQ1_val (by omega_arith) hW hge hle (wv_lt _ _ _ _) (Bool.toNat_lt b) hv₃ (wv_lt _ _ _ _)
    (Bool.toNat_lt c1) hv₅
  have hlow : wv t₅.mem B et w = wv t₅.mem B et (w + 1) := by
    have hlt : wv t₅.mem B et (w + 1) < 2 ^ (64 * w) := by
      rw [hT3]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hMw
    rw [wv_succ] at hlt ⊢
    have : (word t₅.mem B (et + 8 * w)).toNat = 0 := by
      by_contra h
      have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 1 ≤ (word t₅.mem B (et + 8 * w)).toNat by omega_arith)
      omega_arith
    rw [this, Nat.mul_zero, Nat.add_zero]
  have f₃ : Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t₂'.mem t₃.mem :=
    Frm.of_outside ho₃ (by simp)
  have f₅ : Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t₃.mem t₅.mem :=
    Frm.of_outside ho₅ (by simp)
  have f' : Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t₆.mem t'.mem :=
    Frm.of_outside ho' (by simp)
  rw [hm₆] at f'
  have ff := (f₃.trans f₅).trans f'
  rw [hm₂₂] at ff
  refine ⟨?_, ff, ((((k₂.trans k₂').trans k₃).trans k₅).trans (k₆.trans k')).mono (by decide), ?_⟩
  · rw [hc, hm₆, hlow, hT3]
  -- The digit: `q̂`, less one where the step added `m` back.
  have tcx : t'.gpr .rcx = t₂'.gpr .rcx :=
    ((k₆.trans k').gpr (by decide)).trans ((k₅.gpr (by decide)).trans (k₃.gpr (by decide)))
  have t11 : t'.gpr .r11 = t₅.gpr .r11 := (k₆.trans k').gpr (by decide)
  rw [tcx, t11, h11₅, BitVec.toNat_add, h2'cx]
  have hd := Bignum.LongDivision.digit_eq (by omega_arith) hW hge hle (wv_lt _ _ _ _) (Bool.toNat_lt b) hv₃
  generalize hqh : min (((word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 128 + (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ 64 +
    (word t.mem B (ex + 8 * (w - 3))).toNat) / ((word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 +
      (word t.mem B (em + 8 * (w - 2))).toNat)) (2 ^ 64 - 1) = qh at hd hge hle hv₃ ⊢
  have hq : qh < 2 ^ 64 := by rw [← hqh]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  by_cases hN : 2 ^ 63 ≤ (word t₃.mem B (et + 8 * w)).toNat
  · simp only [(top_half t₃.mem B et w).mpr hN, ↓reduceIte] at hd
    simp only [hN, decide_true]
    have h1 : 1 ≤ qh := by
      rcases Nat.eq_zero_or_pos qh with h0 | h0
      · exfalso
        subst h0
        have hyM : (X * 2 ^ 64 + g) / M = 0 := by omega_arith
        have := (top_half t₃.mem B et w).mpr hN
        have hlt : X * 2 ^ 64 + g < M := (Nat.div_eq_zero_iff_lt (by omega_arith)).mp hyM
        have := wv_lt t₃.mem B et (w + 1)
        have : wv t₃.mem B et (w + 1) ≤ X * 2 ^ 64 + g := by
          rw [Nat.zero_mul, Nat.add_zero] at hv₃
          cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv₃ <;>
            omega_arith
        have : M < 2 ^ (64 * (w + 1)) / 2 := by omega_arith
        omega_arith
      · exact h0
    rw [show (mask true).toNat = 2 ^ 64 - 1 from rfl, show qh + (2 ^ 64 - 1) = (qh - 1) + 2 ^ 64 by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    exact hd
  · simp only [show ¬ (2 ^ (64 * (w + 1)) / 2 ≤ wv t₃.mem B et (w + 1)) from fun h => hN ((top_half _ _ _ _).mp h),
      ↓reduceIte] at hd
    simp only [hN, decide_false]
    rw [show (mask false).toNat = 0 from rfl, Nat.add_zero, Nat.mod_eq_of_lt hq]
    exact hd

/-- A normalized remainder step: `x := (x 2^64 + digit) mod m`. -/
theorem step_ok {t : State} {B : Addr} {Z w ex em et ev : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h8 : t.gpr .r8 = off B et)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hbp : t.gpr .rbp = off B ev)
    (hw : 3 ≤ w) (hw' : w < 2 ^ 30)
    (hXz : ex + 8 * w ≤ Z) (hMz : em + 8 * w ≤ Z) (hTz : et + 8 * (w + 1) ≤ Z) (hE : ev + 16 ≤ Z)
    (sepX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et)
    (sepM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et)
    (hd : 2 ^ 63 ≤ (word t.mem B (em + 8 * (w - 1))).toNat)
    (hv : (word t.mem B ev).toNat =
      (2 ^ 128 - 1) / (word t.mem B (em + 8 * (w - 1))).toNat - 2 ^ 64)
    (hx : wv t.mem B ex w < wv t.mem B em w) :
    WP isa Impl.Rsa.X86_64.WordReduce.step t fun t' =>
      wv t'.mem B ex w = (wv t.mem B ex w * 2 ^ 64 + (word t.mem B (ev + 8)).toNat) % wv t.mem B em w ∧
      Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t.mem t'.mem ∧ Keep mmRegs t t' :=
  WP.mono (stepQ_ok hs hbx h10 h8 h12 hbp hw hw' hXz hMz hTz hE sepX sepM hd hv hx) fun _ ⟨a, b, c, _⟩ => ⟨a, b, c⟩

end VG.Proof.Rsa.X86_64.WordReduce
