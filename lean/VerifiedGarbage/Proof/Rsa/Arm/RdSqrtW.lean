module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdHalve
public import VerifiedGarbage.Proof.Rsa.Arm.KdTop

import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.Arm.RdTaint
import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Bignum.SqrtRem
import VerifiedGarbage.Proof.Bignum.WordStepNorm32
public import VerifiedGarbage.Proof.Bignum.WordStep32
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.Arm.KdRun
import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Framework.Arm.Keep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.ShiftK
import VerifiedGarbage.Proof.Bignum.Arm.CopyWords
import VerifiedGarbage.Proof.Bignum.Arm.SubState

/-! # `vg_rsa_recover_primes_det` on ARMv7: the square root by words

The operations over a prefix of the wide arrays (`KS.copyN_W`, `KS.subN_W`, `KS.selN_W`, …) for
arrays whose numbers fit the prefix, and the square root (`sqrt_vp`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr aW)
open VG.Proof.Rsa (sub32 b2n)

/-! ## Prefixes -/

theorem val32_prefix (m : Mem) (B : BitVec 32) {W o n : Nat} (hn : n ≤ W) :
    val32 m (State.addr B) (arr W o) n = num m B W o % 2 ^ (32 * n) := by
  rw [numW_at m B W o n hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

/-- A write of `[o]`'s low `n` words, its words above them zero before. -/
theorem num_prefix_write {m m' : Mem} {B : BitVec 32} {W o n : Nat} (hn : n ≤ W)
    (O : Outside (State.addr B) (arr W o) (4 * n) m m') (hf : arr W o + 4 * W ≤ 2 ^ 64)
    (h0 : num m B W o < 2 ^ (32 * n)) : num m' B W o = val32 m' (State.addr B) (arr W o) n := by
  have e := numW_at m B W o n hn
  have hi : val32 m (State.addr B) (arr W o + 4 * n) (W - n) = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m (State.addr B) (arr W o + 4 * n) (W - n)) with c | c
    · exact c
    · have := Nat.mul_le_mul_left (2 ^ (32 * n)) c; omega
  rw [numW_at m' B W o n hn, O.val32 (d := arr W o + 4 * n) (k := W - n) (Or.inr (by omega)) (by omega), hi,
    Nat.mul_zero, Nat.add_zero]


section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.prefix_val (h : KS P σ A live AW liveW V ls s) {a n : Nat} (ha : a ∈ liveW) (hn : n ≤ P.W)
    (hza : AW a < 2 ^ (32 * n)) : val32 s.mem (State.addr P.B) (arr P.W a) n = AW a := by
  rw [val32_prefix _ _ hn, h.arrsW a ha, Nat.mod_eq_of_lt hza]

/-- `copyN o a` over `n` words (`lr`), both numbers below `2^(32 n)`. -/
theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.copyN_W {o a n : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (ha : a ∈ liveW) (hoa : o ≠ a) (hl : ∀ j ∈ live, j / 2 ≠ o) (hn : 0 < n) (hnW : n ≤ P.W)
    (hlr : s.gpr .lr = BitVec.ofNat 32 n) (hza : AW a < 2 ^ (32 * n))
    (hzo : num s.mem P.B P.W o < 2 ^ (32 * n)) :
    WP isa (copyN o a) s fun t => KS P σ A live (upd AW o (AW a)) (o :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t := by
  have sz := h.sizes
  have fo := fit_W sz ho
  simp only [S] at fo
  refine WP.mono (Keys.copyN_ok hv ho (h.liveW_lt a ha) (by decide) hoa hn hnW (Or.inr ⟨rfl, hlr⟩)) fun t ⟨ht, O, v, r⟩ => ?_
  have kk : Keep P.B P.W [o] [] s.mem t.mem := Keep.of_arr (d := 0) (by simpa using O)
    (by have : S P.W = 4 * (P.W + 2) := rfl; omega) (List.mem_singleton_self o)
  refine ⟨h.write_W kk ho (by simp)
    (h.r8_of r) r.sp r.rd r.wr ?_ hl (by simp), ht, r⟩
  rw [num_prefix_write hnW O (by omega) hzo, v, h.prefix_val ha hnW hza]

/-- `subN o a b` over `n` words: `[o] := [a] - [b]` modulo `2^(32 n)`, and the borrow. -/
theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.subN_W {o a b n : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hoa : o ≠ a) (hob : o ≠ b) (hl : ∀ j ∈ live, j / 2 ≠ o)
    (hn : 0 < n) (hnW : n ≤ P.W) (hlr : s.gpr .lr = BitVec.ofNat 32 n) (hza : AW a < 2 ^ (32 * n))
    (hzb : AW b < 2 ^ (32 * n)) (hzo : num s.mem P.B P.W o < 2 ^ (32 * n)) :
    WP isa (subN o a b) s fun t => KS P σ A live (upd AW o (sub32 n (AW a) (AW b))) (o :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t ∧ (t.gpr .r11).toNat = b2n (decide (AW a < AW b)) := by
  have sz := h.sizes
  have fo := fit_W sz ho
  simp only [S] at fo
  refine WP.mono (Keys.subN_ok hv ho (h.liveW_lt a ha) (h.liveW_lt b hb) (by decide) hoa hob hn hnW (Or.inr ⟨rfl, hlr⟩))
    fun t ⟨ht, O, v, c, r⟩ => ?_
  rw [h.prefix_val ha hnW hza, h.prefix_val hb hnW hzb] at v
  obtain ⟨xv, cv⟩ := VG.Proof.Rsa.sub32_of (val32_lt _ _ _ _) hzb v c
  have kk : Keep P.B P.W [o] [] s.mem t.mem := Keep.of_arr (d := 0) (by simpa using O)
    (by have : S P.W = 4 * (P.W + 2) := rfl; omega) (List.mem_singleton_self o)
  refine ⟨h.write_W kk ho (by simp)
    (h.r8_of r) r.sp r.rd r.wr ?_ hl (by simp), ht, r, cv⟩
  rw [num_prefix_write hnW O (by omega) hzo, xv]

/-- `selN o a b sl` over `n` words. -/
theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.selN_W {o a b sl n : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ ls)
    (bit : V sl ≤ 1) (hl : ∀ j ∈ live, j / 2 ≠ o)
    (hn : 0 < n) (hnW : n ≤ P.W) (hlr : s.gpr .lr = BitVec.ofNat 32 n) (hza : AW a < 2 ^ (32 * n))
    (hzb : AW b < 2 ^ (32 * n)) (hzo : num s.mem P.B P.W o < 2 ^ (32 * n)) :
    WP isa (selN o a b sl) s fun t =>
      KS P σ A live (upd AW o (if V sl = 0 then AW a else AW b)) (o :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t := by
  have sz := h.sizes
  have fo := fit_W sz ho
  simp only [S] at fo
  have hs := h.sl sl hsl
  refine WP.mono (Keys.selN_ok hv ho (h.liveW_lt a ha) (h.liveW_lt b hb) (by decide) hoa hob
    (h.ls_ok sl hsl).1 (by rw [hs]; exact bit) hn hnW (Or.inr ⟨rfl, hlr⟩)) fun t ⟨ht, O, v, r⟩ => ?_
  have kk : Keep P.B P.W [o] [] s.mem t.mem := Keep.of_arr (d := 0) (by simpa using O)
    (by have : S P.W = 4 * (P.W + 2) := rfl; omega) (List.mem_singleton_self o)
  refine ⟨h.write_W kk ho (by simp)
    (h.r8_of r) r.sp r.rd r.wr ?_ hl (by simp), ht, r⟩
  rw [num_prefix_write hnW O (by omega) hzo, v, hs, h.prefix_val ha hnW hza, h.prefix_val hb hnW hzb]

end

/-! ## A digit's estimate -/

open VG.Proof.Bignum.SqrtRem in
/-- The true digit where `R ≥ 2 s β²`: `β - 1`. -/
theorem digit_edge {β s R q : Nat} (hβ : 1 ≤ β) (hs : β ≤ 2 * s) (hR : 2 * s * β * β ≤ R)
    (hq : IsDigit β s R q) (hqb : q < β) : q = β - 1 := by
  refine Nat.le_antisymm (by omega) (Nat.le_of_not_lt fun h => ?_)
  have hq2 : R < (2 * s * β + (q + 1)) * (q + 1) := hq.2
  obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  generalize 2 * s = t at hs hR hq2
  have h1 : (t * (b + 1) + (q + 1)) * (q + 1) ≤ (t * (b + 1) + b) * b :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (t * (b + 1) + b) * b ≤ t * (b + 1) * (b + 1) := by
    have e1 : (t * (b + 1) + b) * b = t * (b + 1) * b + b * b := by ring
    have e2 : t * (b + 1) * (b + 1) = t * (b + 1) * b + t * (b + 1) := by ring
    have : b * b ≤ t * (b + 1) := Nat.le_trans (Nat.mul_le_mul (Nat.le_succ b) (Nat.le_refl b))
      (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega))
    omega
  omega

/-- `⌊R / 2T⌋`'s top word is at most `⌊s / T⌋`, `s β / T`'s. -/
theorem u2_le {s R T : Nat} (_hT : 0 < T) (hR : R < (2 * s + 1) * 2 ^ 64) :
    R / (2 * T) / 2 ^ 64 ≤ s * 2 ^ 32 / T / 2 ^ 32 := by
  have eL : R / (2 * T) / 2 ^ 64 = R / 2 ^ 64 / (2 * T) := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have eR : s * 2 ^ 32 / T / 2 ^ 32 = s / T := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_div_mul_right _ _ (by decide)]
  rw [eL, eR]
  have : R / 2 ^ 64 ≤ 2 * s := by
    have := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 64)).mpr hR; omega
  calc R / 2 ^ 64 / (2 * T) ≤ 2 * s / (2 * T) := Nat.div_le_div_right this
    _ = s / T := Nat.mul_div_mul_left _ _ (by decide)

/-- `⌊R / 2T⌋ < (β + 1) ⌊s β / T⌋` for a normalized `s` (`β T ≤ 2 s`), `T` 1 or at least `β`. -/
theorem u_lt {s R T : Nat} (hT : T = 1 ∨ 2 ^ 32 ≤ T) (hs : 2 ^ 32 * T ≤ 2 * s) (hR : R < (2 * s + 1) * 2 ^ 64) :
    R / (2 * T) < (2 ^ 32 + 1) * (s * 2 ^ 32 / T) := by
  rcases hT with rfl | hT
  · rw [Nat.div_one, Nat.mul_one]
    refine (Nat.div_lt_iff_lt_mul (by decide)).mpr ?_
    omega
  · have hT0 : 0 < T := by omega
    have d1 := Nat.div_mul_le_self (s * 2 ^ 32) T
    have d2 := Nat.lt_div_mul_add (a := s * 2 ^ 32) hT0
    refine (Nat.div_lt_iff_lt_mul (by omega)).mpr ?_
    have e : (2 ^ 32 + 1) * (s * 2 ^ 32 / T) * (2 * T) = 2 * (2 ^ 32 + 1) * (s * 2 ^ 32 / T * T) := by ring
    rw [e]
    generalize s * 2 ^ 32 / T * T = X at d1 d2 ⊢
    omega

open VG.Proof.Bignum.SqrtRem VG.Proof.Bignum.WordStep32 in
/-- The estimates of a digit of the square root, for `s` of `j ≥ 1` words, normalized, `T = β^(j-1)`,
`R = r β² + P`, `U = ⌊R / 2T⌋` (the top three words of `⌊R / 2⌋`) and `D = ⌊s β / T⌋` (the top two
of `s β`): `quot`'s and `refine3`'s conditions, the 2-by-1 estimate within 2 above
`Q = min(⌊U / D⌋, β - 1)`, and `q ≤ Q ≤ q + 2` for the digit `q`. -/
theorem sqrt_est {K s R q : Nat} (hK : K = 0 ∨ 32 ≤ K) (hs : 2 ^ 32 * 2 ^ K ≤ 2 * s)
    (hR : R < (2 * s + 1) * 2 ^ 64) (hq : IsDigit (2 ^ 32) s R q) (hqb : q < 2 ^ 32) :
    R / (2 * 2 ^ K) / 2 ^ 64 ≤ s * 2 ^ 32 / 2 ^ K / 2 ^ 32 ∧
      R / (2 * 2 ^ K) < (2 ^ 32 + 1) * (s * 2 ^ 32 / 2 ^ K) ∧
      min (R / (2 * 2 ^ K) / (s * 2 ^ 32 / 2 ^ K)) (2 ^ 32 - 1) ≤
        min (R / (2 * 2 ^ K) / 2 ^ 32 / (s * 2 ^ 32 / 2 ^ K / 2 ^ 32)) (2 ^ 32 - 1) ∧
      min (R / (2 * 2 ^ K) / 2 ^ 32 / (s * 2 ^ 32 / 2 ^ K / 2 ^ 32)) (2 ^ 32 - 1) ≤
        min (R / (2 * 2 ^ K) / (s * 2 ^ 32 / 2 ^ K)) (2 ^ 32 - 1) + 2 ∧
      q ≤ min (R / (2 * 2 ^ K) / (s * 2 ^ 32 / 2 ^ K)) (2 ^ 32 - 1) ∧
      min (R / (2 * 2 ^ K) / (s * 2 ^ 32 / 2 ^ K)) (2 ^ 32 - 1) ≤ q + 2 := by
  generalize eK : 2 ^ K = T at hs ⊢
  have hT : T = 1 ∨ 2 ^ 32 ≤ T := by
    rcases hK with rfl | h
    · left; rw [← eK]; rfl
    · right; rw [← eK]; exact Nat.pow_le_pow_right (by decide) h
  have hT0 : 0 < T := by rcases hT with h | h <;> omega
  have s2 : 2 ^ 32 ≤ 2 * s := Nat.le_trans (Nat.le_mul_of_pos_right _ hT0) hs
  refine ⟨u2_le hT0 hR, u_lt hT hs hR, ?_⟩
  have eD2 : s * 2 ^ 32 / T / 2 ^ 32 = s / T := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_div_mul_right _ _ (by decide)]
  have hsT : 2 ^ 31 ≤ s / T := (Nat.le_div_iff_mul_le hT0).mpr (by omega)
  by_cases hY : R < 2 * s * 2 ^ 32 * 2 ^ 32
  · have q3 := qhat3_div (Y := R) (M := 2 * s * 2 ^ 32) (P := 2 ^ 31) (K := K) (by decide) hY (by
      have e : 2 * s * 2 ^ 32 * 2 ^ 31 / 2 ^ (K + 32) = s * 2 ^ 32 / T := by
        rw [Nat.pow_add, eK, show 2 * s * 2 ^ 32 * 2 ^ 31 = s * 2 ^ 32 * 2 ^ 32 by ring,
          Nat.mul_div_mul_right _ _ (by decide)]
      rw [e, eD2]; exact hsT)
    have eU : R * 2 ^ 31 / 2 ^ (K + 32) = R / (2 * T) := by
      rw [Nat.pow_add, eK, show T * 2 ^ 32 = 2 * T * 2 ^ 31 by ring, Nat.mul_div_mul_right _ _ (by decide)]
    have eD : 2 * s * 2 ^ 32 * 2 ^ 31 / 2 ^ (K + 32) = s * 2 ^ 32 / T := by
      rw [Nat.pow_add, eK, show 2 * s * 2 ^ 32 * 2 ^ 31 = s * 2 ^ 32 * 2 ^ 32 by ring,
        Nat.mul_div_mul_right _ _ (by decide)]
    rw [eU, eD] at q3
    obtain ⟨-, a2, a3, a4, a5⟩ := q3
    have d1 := digit_le_div (β := 2 ^ 32) (by omega) hq.1
    have d2 := div_le_digit_succ (β := 2 ^ 32) s2 (by omega) hqb hq.2
    exact ⟨a2, a3, Nat.le_trans d1 a4, Nat.le_trans a5 (Nat.add_le_add_right d2 1)⟩
  · have hY' : 2 * s * 2 ^ 32 * 2 ^ 32 ≤ R := Nat.le_of_not_lt hY
    have qe := digit_edge (by decide) s2 hY' hq hqb
    have hD0 : 0 < s * 2 ^ 32 / T := Nat.div_pos (by
      have := Nat.mul_le_mul_right (2 ^ 32) (show T ≤ s by omega); omega) hT0
    have uD : 2 ^ 32 * (s * 2 ^ 32 / T) ≤ R / (2 * T) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have := Nat.div_mul_le_self (s * 2 ^ 32) T
      calc 2 ^ 32 * (s * 2 ^ 32 / T) * (2 * T) = 2 * 2 ^ 32 * (s * 2 ^ 32 / T * T) := by ring
        _ ≤ 2 * 2 ^ 32 * (s * 2 ^ 32) := Nat.mul_le_mul_left _ this
        _ ≤ R := by rw [show 2 * 2 ^ 32 * (s * 2 ^ 32) = 2 * s * 2 ^ 32 * 2 ^ 32 by ring]; exact hY'
    have m1 : 2 ^ 32 - 1 ≤ R / (2 * T) / (s * 2 ^ 32 / T) := by
      refine (Nat.le_div_iff_mul_le hD0).mpr (Nat.le_trans ?_ uD)
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hd2 : 0 < s * 2 ^ 32 / T / 2 ^ 32 := by rw [eD2]; omega
    have m2 : 2 ^ 32 - 1 ≤ R / (2 * T) / 2 ^ 32 / (s * 2 ^ 32 / T / 2 ^ 32) := by
      refine (Nat.le_div_iff_mul_le hd2).mpr ?_
      have h1 : s * 2 ^ 32 / T ≤ R / (2 * T) / 2 ^ 32 := by
        rw [Nat.le_div_iff_mul_le (by decide), Nat.mul_comm]; exact uD
      have h2 := Nat.div_mul_le_self (s * 2 ^ 32 / T) (2 ^ 32)
      have h3 : (2 ^ 32 - 1) * (s * 2 ^ 32 / T / 2 ^ 32) ≤ s * 2 ^ 32 / T / 2 ^ 32 * 2 ^ 32 := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    rw [Nat.min_eq_right m1, Nat.min_eq_right m2, qe]
    exact ⟨Nat.le_refl _, Nat.le_add_right _ _, Nat.le_refl _, Nat.le_add_right _ _⟩

/-! ## A digit's corrections -/

open VG.Proof.Bignum.WordStep32 (twos twos_eq twos_neg addIfNeg)

/-- One masked correction of a digit estimate `x ∈ [q, q + 2]`: the signed remainder
`v = R - (c + x) x` fits in half the words, is negative exactly where `x` is above the digit
`q`, and adding `c + 2 x - 1` where negative gives the remainder of `x - 1`. -/
theorem sq_fix {W R c q x : Nat} (hqR : (c + q) * q ≤ R) (hRq : R < (c + (q + 1)) * (q + 1))
    (hxq : q ≤ x) (hx : x ≤ q + 2) (hRW : 2 * (R + 1) ≤ W) (hcW : 2 * ((c + (q + 2)) * (q + 2)) < W) :
    -((W : Int) / 2) ≤ (R : Int) - ((c + x) * x : Nat) ∧ (R : Int) - ((c + x) * x : Nat) < (W : Int) / 2 ∧
    ((R : Int) - ((c + x) * x : Nat) < 0 ↔ q < x) ∧
    addIfNeg (c + 2 * x - 1) ((R : Int) - ((c + x) * x : Nat)) =
      (R : Int) - ((c + (x - if q < x then 1 else 0)) * (x - if q < x then 1 else 0) : Nat) := by
  have up : (c + x) * x ≤ (c + (q + 2)) * (q + 2) := Nat.mul_le_mul (by omega) hx
  have neg : (R : Int) - ((c + x) * x : Nat) < 0 ↔ q < x := by
    constructor
    · intro h
      refine Nat.lt_of_le_of_ne hxq fun e => ?_
      subst e; omega
    · intro h
      have : (c + (q + 1)) * (q + 1) ≤ (c + x) * x := Nat.mul_le_mul (by omega) h
      omega
  refine ⟨by omega, by omega, neg, ?_⟩
  unfold addIfNeg
  by_cases h : q < x
  · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    have cs : (c + (y + 1)) * (y + 1) = (c + y) * y + (c + 2 * (y + 1) - 1) := by
      rw [show c + 2 * (y + 1) - 1 = c + 2 * y + 1 by omega]; ring
    simp only [neg.mpr h, h, ↓reduceIte, Nat.add_sub_cancel]
    rw [cs, Nat.cast_add]; omega
  · simp only [show ¬ ((R : Int) - ((c + x) * x : Nat) < 0) from fun e => h (neg.mp e), h, ↓reduceIte,
      Nat.sub_zero, Int.add_zero]

/-! ## The shift stages, wide -/

section
variable {P : RP}

/-- A masked stage, wide: `op` puts `F` into `[t1]`; then `[x] := F` where the bit at `sBit` is set. -/
theorem selStage_vp {x t1 t2 : Nat} {op : Prog isa} {L LW LW' LS LS' : List Nat} {E : State → Prop}
    {A AW V V' : State → Nat → Nat} {F : State → Nat}
    (hx' : x ∈ LW') (hsub : ∀ j ∈ LW', j ∈ LW) (hx22 : x < 22) (ht2 : t2 < 22) (h1x : t1 ≠ x) (h2x : t2 ≠ x)
    (h12 : t2 ≠ t1) (hLWT : ∀ j ∈ LW', j ≠ t1 ∧ j ≠ t2) (hL : ∀ j ∈ L, j / 2 ≠ t2 ∧ j / 2 ≠ x) (hB : sBit ∈ LS')
    (bit : ∀ σ, E σ → V' σ sBit ≤ 1)
    (hop : VP (Dk P E A L AW LW V LS P.W 22) op
      (Dk P E A L (fun σ => upd (AW σ) t1 (F σ)) (t1 :: LW) V' LS' P.W 22))
    (cS : DCert (sel t2 x t1 sBit)) (cC : DCert (copy x t2)) :
    VP (Dk P E A L AW LW V LS P.W 22) (selStage op x t1 t2)
      (Dk P E A L (fun σ => upd (AW σ) x (if V' σ sBit = 0 then AW σ x else F σ)) LW' V' LS' P.W 22) := by
  have hx := hsub x hx'
  simp only [selStage, seqs]
  refine hop.seq ((selW_vp (o := t2) (a := x) (b := t1) (sl := sBit) ht2 (List.mem_cons_of_mem _ hx)
    (List.mem_cons_self ..) h2x h12 hB bit (fun j hj => (hL j hj).1) cS).seq ?_)
  refine (copyW_vp (o := x) (a := t2) hx22 (List.mem_cons_self ..) (Ne.symm h2x) (fun j hj => (hL j hj).2)
    cC).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩)
      (fun j hj => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub j hj))), ?_⟩)
      (fun d hd => ⟨hd, rfl⟩), hv⟩
  obtain ⟨j1, j2⟩ := hLWT j hj
  by_cases c : j = x
  · subst c; simp only [upd_self, upd_ne _ _ (Ne.symm h1x)]
  · simp only [upd_ne _ _ c, upd_ne _ _ j1, upd_ne _ _ j2]

end

theorem even_div_pow {t i : Nat} (hi : 1 ≤ i) : 2 * (t / 2) / 2 ^ i = t / 2 ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_div_mul_left _ _ (by decide), Nat.div_div_eq_div_mul,
    Nat.mul_comm]

section
variable {P : RP}

/-- The normalization's bit stage `i` (`1 ≤ i < 5`): `[wR]` shifted left by `2^i` bits where bit `i` of
`t` (at `sLz`) is set. -/
theorem normBitStage_vp {i : Nat} (hi1 : 1 ≤ i) (hi : i < 5) {L LW LS : List Nat} {E : State → Prop}
    {A AW V : State → Nat → Nat} {X t : State → Nat}
    (hR : wR ∈ LW) (hLWT : ∀ j ∈ LW, j ≠ wG ∧ j ≠ wF) (hL : ∀ j ∈ L, j / 2 ≠ wG ∧ j / 2 ≠ wF ∧ j / 2 ≠ wR)
    (hS : sLz ∈ LS) (vR : ∀ σ, E σ → AW σ wR = X σ * 2 ^ (2 * (t σ / 2) % 2 ^ i) % 2 ^ (32 * P.W))
    (vS : ∀ σ, E σ → V σ sLz = t σ) :
    VP (Dk P E A L AW LW V LS P.W 22) (normBitStage i)
      (Dk P E A L (fun σ => upd (AW σ) wR (X σ * 2 ^ (2 * (t σ / 2) % 2 ^ (i + 1)) % 2 ^ (32 * P.W))) LW
        (fun σ => upd (upd (V σ) sBit (t σ / 2 ^ i % 2)) sK 0) (sK :: sBit :: LS) P.W 22) := by
  have p : 2 ^ i < 32 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (show i ≤ 4 by omega)) (by decide)
  simp only [normBitStage, seqs]
  refine VP.seq (G := Dk P E A L AW LW (fun σ => upd (V σ) sBit (t σ / 2 ^ i % 2)) (sBit :: LS) P.W 22)
    (VP.dctx (bitToLz_taint i hi1 hi) (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      WP.mono (bitTo_ok (by omega) hS h hv) fun y ⟨hy, hvy⟩ => ⟨e, by rwa [vS σ e] at hy, hvy⟩) ?_
  refine (copyW_vp (o := wG) (a := wR) (by decide) hR (by decide) (fun j hj => (hL j hj).1) copyGR_taint).seq ?_
  refine (selStage_vp (x := wR) (t1 := wG) (t2 := wF) (LW' := LW) (F := fun σ => AW σ wR * 2 ^ (2 ^ i) % 2 ^ (32 * P.W))
    hR (fun j hj => List.mem_cons_of_mem _ hj) (by decide) (by decide) (by decide) (by decide) (by decide) hLWT
    (fun j hj => ⟨(hL j hj).2.1, (hL j hj).2.2⟩) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (fun σ _ => by simp only [upd_ne _ _ (show sBit ≠ sK by decide), upd_self]
                   exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    ((shlK_vp (j := wG) (k := 2 ^ i) ⟨Nat.two_pow_pos _, p⟩ (List.mem_cons_self ..)
      (fun j hj => (hL j hj).1) (shlKG_taint i hi)).mono (fun _ _ h => h)
      fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp only [List.mem_cons] at hj ⊢; grind, by simp only [upd_self]⟩)
        (fun d hd => ⟨hd, rfl⟩), hv⟩)
    selFRG_taint copyRF_taint).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩)
      (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩), hv⟩
  by_cases c : j = wR
  · subst c
    simp only [upd_self, upd_ne _ _ (show sBit ≠ sK by decide), upd_ne _ _ (show wR ≠ wG by decide)]
    rw [vR σ e, ← even_div_pow (t := t σ) hi1]
    exact shift_sel_mul _ _ _ _
  · simp only [upd_ne _ _ c, upd_ne _ _ (hLWT j hj).1]

end

/-! ## The word stages, wide -/

/-- The wide word stages' count: `2^KWW ≥ W`. -/
abbrev KWW (P : RP) : Nat := Nat.log2 (P.W - 1) + 1

section
variable {P : RP}

theorem kww_pow {m : Nat} (hm : m < KWW P) : 2 ^ m < P.W := by
  have w2 : 2 ≤ P.W := by simp only [RP.W]; omega
  have := Nat.log2_self_le (n := P.W - 1) (by omega)
  have := Nat.pow_le_pow_right (n := 2) (by decide) (show m ≤ Nat.log2 (P.W - 1) by simp only [KWW] at hm; omega)
  omega

theorem kww_ge : P.W ≤ 2 ^ KWW P := by
  have := Nat.lt_log2_self (n := P.W - 1)
  simp only [KWW]; omega

theorem stageNext_ok {m q : Nat} {LS : List Nat} {σ s : State} {A AW V : Nat → Nat} {L LW : List Nat}
    (hm : 2 ^ m < P.W) (hT : sTk ∈ LS) (hW : sWs ∈ LS) (vT : V sTk = q / 2 ^ m) (vW : V sWs = 4 * 2 ^ m)
    (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.W 22) :
    WP isa (.block stageNext) s fun t =>
      (KS P σ A L AW LW (upd (upd V sTk (q / 2 ^ (m + 1))) sWs (4 * 2 ^ (m + 1))) (sWs :: sTk :: LS) t ∧
        Ws t P.B P.Z P.W 22) ∧ t.z = decide (KWW P - (m + 1) = 0) := by
  have sz := h.sizes
  have Wl := sz.Wle
  have w2 : 2 ≤ P.W := by simp only [RP.W]; omega
  have p1 : 2 ^ (m + 1) ≤ 2 * P.W := by rw [Nat.pow_succ]; omega
  have b1 : q / 2 ^ m < 2 ^ 32 := by rw [← vT, ← h.sl sTk hT]; exact BitVec.isLt _
  unfold stageNext
  refine h.ldrSlot hv (d := sTk) hT (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2.strSlot hv2 (d := sTk) (r := .r1) (by decide) fun s3 h3 hv3 g3 _ => ?_
  refine h3.ldrSlot hv3 (d := sWs) (by simp [hW]) (r := .r1) (by decide) fun s7 h7 hv7 u7 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s8 u8 => ?_
  obtain ⟨h8, hv8⟩ := h7.reg hv7 (u8.rest (ws := [.r1]) (by simp)) u8.mem
  refine h8.strSlot hv8 (d := sWs) (r := .r1) (by decide) fun s9 h9 hv9 g9 _ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s10 u10 => ?_
  obtain ⟨h10, hv10⟩ := h9.reg hv9 (u10.rest (ws := [.r1]) (by simp)) u10.mem
  refine wp_mov (op2_lsr (by decide)) fun s11 u11 => ?_
  obtain ⟨h11, hv11⟩ := h10.reg hv10 (u11.rest (ws := [.r1]) (by simp)) u11.mem
  refine wp_cmp (op2_imm (by decide)) fun t ut zt => WP.block_nil ?_
  obtain ⟨ht, hvt⟩ := h11.reg hv11 (ut.rest []) ut.mem
  have e2 : (s2.gpr .r1).toNat = q / 2 ^ (m + 1) := by rw [u2.gpr, u1.gpr]; exact halfSlot vT b1
  have e8 : (s8.gpr .r1).toNat = 4 * 2 ^ (m + 1) := by
    rw [u8.gpr, u7.gpr]
    simp only [upd_ne _ _ (show sWs ≠ sTk by decide), vW]
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_succ, Nat.pow_succ 2 m,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have r11v : s11.gpr .r1 = if 4 * 2 ^ (m + 1) < 4 * P.W then 1 else 0 := by
    rw [u11.gpr, u10.gpr, dpVal, hv9.r9, g9]
    rw [show s8.gpr .r1 = BitVec.ofNat 32 (4 * 2 ^ (m + 1)) from BitVec.eq_of_toNat_eq (by
      rw [e8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])]
    rw [show BitVec.ofNat 32 P.W <<< 2 = BitVec.ofNat 32 (4 * P.W) from BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (a := P.W) (by omega)]; omega)]
    exact sign_bit (by omega) (by omega)
  refine ⟨⟨ht.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨?_, ?_⟩), hvt⟩, ?_⟩
  · simp only [List.mem_cons] at hd ⊢; grind
  · rw [e8, e2]
  · rw [zt, r11v]
    have e : 4 * 2 ^ (m + 1) < 4 * P.W ↔ m + 1 ≤ Nat.log2 (P.W - 1) := by
      rw [Nat.le_log2 (by omega)]; omega
    by_cases c : m + 1 ≤ Nat.log2 (P.W - 1)
    · simp only [e.mpr c, ↓reduceIte]
      have : ¬ KWW P - (m + 1) = 0 := by simp only [KWW]; omega
      simp only [this, decide_false]; rfl
    · simp only [show ¬ 4 * 2 ^ (m + 1) < 4 * P.W from fun h => c (e.mp h), ↓reduceIte]
      have : KWW P - (m + 1) = 0 := by simp only [KWW]; omega
      simp only [this, decide_true]; rfl

end

/-- The word stages' slots after `m` stages: `q / 2^m` and `4 · 2^m`. -/
def WSV (V0 : Nat → Nat) (q m : Nat) : Nat → Nat := upd (upd V0 sTk (q / 2 ^ m)) sWs (4 * 2 ^ m)
abbrev LSS (LS0 : List Nat) : List Nat := sWs :: sTk :: LS0

section
variable {P : RP}

/-- A word stage, wide: `[x] := G (m + 1)` from `G m` by `op` (into `[wG]`) where bit `m` of `q` is set. -/
theorem wordStageG_vp {x m : Nat} {op : Prog isa} (hm : m < KWW P) {L LW LS0 : List Nat} {E : State → Prop}
    {A AW0 V0 : State → Nat → Nat} {G : Nat → State → Nat} {q F : State → Nat}
    (hx : x ∈ LW) (hx22 : x < 22) (hxG : x ≠ wG ∧ x ≠ wF) (hLWT : ∀ j ∈ LW, j ≠ wG ∧ j ≠ wF)
    (hL : ∀ j ∈ L, j / 2 ≠ wG ∧ j / 2 ≠ wF ∧ j / 2 ≠ x) (hLS : ∀ d ∈ LS0, d ≠ sBit ∧ d ≠ sTk ∧ d ≠ sWs)
    (hop : VP (Dk P E A L (fun σ => upd (AW0 σ) x (G m σ)) LW
        (fun σ => upd (WSV (V0 σ) (q σ) m) sBit (q σ / 2 ^ m % 2)) (sBit :: LSS LS0) P.W 22) op
      (Dk P E A L (fun σ => upd (upd (AW0 σ) x (G m σ)) wG (F σ)) (wG :: LW)
        (fun σ => upd (WSV (V0 σ) (q σ) m) sBit (q σ / 2 ^ m % 2)) (sBit :: LSS LS0) P.W 22))
    (hstep : ∀ σ, E σ → (if q σ / 2 ^ m % 2 = 0 then G m σ else F σ) = G (m + 1) σ)
    (cS : DCert (sel wF x wG sBit)) (cC : DCert (copy x wF)) :
    VP (Dk P E A L (fun σ => upd (AW0 σ) x (G m σ)) LW (fun σ => WSV (V0 σ) (q σ) m) (LSS LS0) P.W 22)
      (seqs [.block (bitTo sTk 0), selStage op x wG wF, .block stageNext])
      (fun σ s => Dk P E A L (fun σ => upd (AW0 σ) x (G (m + 1) σ)) LW (fun σ => WSV (V0 σ) (q σ) (m + 1))
        (LSS LS0) P.W 22 σ s ∧ s.z = decide (KWW P - (m + 1) = 0)) := by
  have hm' := kww_pow hm
  simp only [seqs]
  refine VP.seq (G := Dk P E A L (fun σ => upd (AW0 σ) x (G m σ)) LW
      (fun σ => upd (WSV (V0 σ) (q σ) m) sBit (q σ / 2 ^ m % 2)) (sBit :: LSS LS0) P.W 22)
    (VP.dctx bitToTk_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      WP.mono (bitTo_ok (i := 0) (by omega) (by simp) h hv) fun y ⟨hy, hvy⟩ =>
        ⟨e, by
          have e1 : WSV (V0 σ) (q σ) m sTk = q σ / 2 ^ m := by simp only [WSV]; rd_up
          simp only [e1, Nat.pow_zero, Nat.div_one] at hy; exact hy, hvy⟩) ?_
  refine (selStage_vp (x := x) (t1 := wG) (t2 := wF) (LW' := LW) (F := F) hx (fun j hj => hj) hx22 (by decide)
    (Ne.symm hxG.1) (Ne.symm hxG.2) (by decide) hLWT (fun j hj => ⟨(hL j hj).2.1, (hL j hj).2.2⟩)
    (List.mem_cons_self ..) (fun σ _ => by simp only [upd_self]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    hop cS cC).seq ?_
  refine VP.dctx stageNext_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
    WP.mono (stageNext_ok (q := q σ) hm' (by simp) (by simp) (by simp only [WSV]; rd_up)
      (by simp only [WSV]; rd_up) h hv)
      fun t ⟨⟨ht, hvt⟩, z⟩ => ⟨⟨e, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨?_, ?_⟩),
        hvt⟩, z⟩
  · by_cases c : j = x
    · subst c; simp only [upd_self, upd_self]; exact hstep σ e
    · simp only [upd_ne _ _ c]
  · simp only [LSS, List.mem_cons] at hd ⊢; grind
  · simp only [WSV]
    simp only [LSS, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · rd_up
    · rd_up
    · obtain ⟨a1, a2, a3⟩ := hLS d hd
      simp only [upd_ne _ _ a1, upd_ne _ _ a2, upd_ne _ _ a3]

end

section
variable {P : RP}

/-- The normalization's word stage `m`. -/
theorem normWordStage_vp {m : Nat} (hm : m < KWW P) {L LW LS0 : List Nat} {E : State → Prop}
    {A AW0 V0 : State → Nat → Nat} {X c q : State → Nat}
    (hR : wR ∈ LW) (hz : wZ ∈ LW) (z0 : ∀ σ, E σ → AW0 σ wZ = 0) (hLWT : ∀ j ∈ LW, j ≠ wG ∧ j ≠ wF)
    (hL : ∀ j ∈ L, j / 2 ≠ wG ∧ j / 2 ≠ wF ∧ j / 2 ≠ wR) (hLS : ∀ d ∈ LS0, d ≠ sBit ∧ d ≠ sTk ∧ d ≠ sWs) :
    VP (Dk P E A L (fun σ => upd (AW0 σ) wR (X σ * 2 ^ (c σ + 32 * (q σ % 2 ^ m)) % 2 ^ (32 * P.W))) LW
        (fun σ => WSV (V0 σ) (q σ) m) (LSS LS0) P.W 22)
      normWordStage
      (fun σ s => Dk P E A L (fun σ => upd (AW0 σ) wR (X σ * 2 ^ (c σ + 32 * (q σ % 2 ^ (m + 1))) % 2 ^ (32 * P.W)))
        LW (fun σ => WSV (V0 σ) (q σ) (m + 1)) (LSS LS0) P.W 22 σ s ∧ s.z = decide (KWW P - (m + 1) = 0)) := by
  have hm' := kww_pow hm
  have hz' : wR ≠ wZ := by decide
  refine wordStageG_vp (G := fun m σ => X σ * 2 ^ (c σ + 32 * (q σ % 2 ^ m)) % 2 ^ (32 * P.W))
    (F := fun σ => X σ * 2 ^ (c σ + 32 * (q σ % 2 ^ m)) % 2 ^ (32 * P.W) % 2 ^ (32 * (P.W - 2 ^ m)) * 2 ^ (32 * 2 ^ m))
    hm hR (by decide) (by decide) hLWT hL hLS ?_ (fun σ _ => shift_sel_mulW _ _ _ _ _ (by omega))
    selFRG_taint copyRF_taint
  refine (shiftUpBy_vp (d := sWs) (sh := 2 ^ m) (o := wG) (a := wR) hm' (by decide) hR (by decide) hz (by decide)
    (fun j hj => (hL j hj).1) (by simp) (fun σ e => by rw [upd_ne _ _ (Ne.symm hz')]; exact z0 σ e)
    (fun σ _ => by simp only [upd_ne _ _ (show sWs ≠ sBit by decide), WSV]; rd_up)
    copyGZ_taint ptrG_taint upBR_taint).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ =>
      ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, by simp only [upd_self]⟩) (fun d hd => ⟨hd, rfl⟩), hv⟩

end

/-! ## The root's stages, over its `W / 2` words -/

theorem lsr1_val {W : Nat} (hW : W < 2 ^ 32) : BitVec.ofNat 32 W >>> 1 = BitVec.ofNat 32 (W / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt (by omega), Nat.pow_one]

/-- `halfKHN j k`, `r11 = 0`: `[j]`'s low `W / 2` words shifted right by `k`, and the word above them cleared. -/
theorem halfKHN_ok {k : Nat} (hk : 0 < k ∧ k < 32) {s : State} {B : BitVec 32} {Z W N j : Nat} (h : Ws s B Z W N) (hj : j < N) (hN : N ≤ 256)
    (hW : 2 ≤ W) (r11 : s.gpr .r11 = 0) :
    WP isa (halfKHN j k) s fun t => Ws t B Z W N ∧ Outside (State.addr B) (arr W j) (4 * (W / 2 + 1)) s.mem t.mem ∧
      val32 t.mem (State.addr B) (arr W j) (W / 2 + 1) = val32 s.mem (State.addr B) (arr W j) (W / 2) / 2 ^ k ∧
      Rest opRegs s t := by
  have fit := h.arr_fit hj
  have hS : S W = 4 * (W + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  rw [halfKHN, WP.seq_iff]
  refine ptr_ok h (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  have l2 : s2.gpr .lr = BitVec.ofNat 32 (W / 2) := by rw [u2.gpr, h1.r9, lsr1_val (by omega)]
  have h2 : Ws s2 B Z W N := h1.of_upd u2 (by decide) (by decide) (by decide)
  refine wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
  have a3 : State.addr (s3.gpr .r1 + BitVec.ofNat 32 0) = off (State.addr B) (arr W j + 4 * (W / 2)) := by
    have e : s3.gpr .r1 = B + BitVec.ofNat 32 (arr W j + 4 * (W / 2)) := by
      rw [u3.gpr, dpVal, u2.other .r0 (by decide), p1, l2]
      have : BitVec.ofNat 32 (W / 2) <<< 2 = BitVec.ofNat 32 (4 * (W / 2)) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
      rw [this, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [e, Offset.add_add, Nat.add_zero]
    exact h.addr (by omega)
  have h3 : Ws s3 B Z W N := h2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_str (by decide) a3 (h3.write (by omega)) fun u u4 => WP.block_nil ?_
  have hu : Ws u B Z W N := h3.of_mupd u4
  have e11 : s3.gpr .r11 = 0 := by
    rw [u3.other .r11 (by decide), u2.other .r11 (by decide), r1.gpr _ (by decide), r11]
  have mu : u.mem = s.mem.writeW (off (State.addr B) (arr W j + 4 * (W / 2))) (0 : BitVec 32) := by
    rw [u4.mem, u3.mem, u2.mem, m1, e11]
  have restU : Rest opRegs s u :=
    (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest _)))
  have outS := writeW32_outside s.mem (State.addr B) (d := arr W j + 4 * (W / 2)) (0 : BitVec 32) (by omega)
  rw [← mu] at outS
  refine WP.mono (VG.Proof.Bignum.Arm.shiftRightK_ok hk u (base := B) (size := Z) (o := arr W j) (n := W / 2)
    ⟨nw, by omega, hu.writable⟩ (by omega)
    (by rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), p1])
    (by rw [u4.gpr, u3.other _ (by decide), l2])) ?_
  intro t inv
  have top : w32 u.mem (State.addr B) (arr W j + 4 * (W / 2)) = 0 := by
    rw [mu, w32_write_self]; rfl
  have res := inv.result hk (by omega)
  have low := outS.val32 (d := arr W j) (k := W / 2) (by omega) (by omega)
  have topT : w32 t.mem (State.addr B) (arr W j + 4 * (W / 2)) = 0 := by
    rw [inv.outside.w32 (Or.inr (by omega)) (by omega), top]
  refine ⟨hu.rest inv.rest, (outS.mono (by omega) (by omega)).trans (inv.outside.mono (by omega) (by omega)),
    ?_, restU.trans (inv.rest.mono (by simp))⟩
  rw [val32_succ, topT, res, low, top]
  simp only [Nat.zero_mod, Nat.mul_zero, Nat.add_zero]

open VG.Proof.Bignum.Arm (SubCtx copyWords_ok) in
/-- `shiftDownBH o`: from `[a]`'s address in `r10` and `4 sh` in `r1`, `[a]`'s words from `sh` below
`W / 2` into `[o]`'s low `W / 2 - sh`. -/
theorem shiftDownBH_ok {s : State} {B : BitVec 32} {Z W N o a sh : Nat} (h : Ws s B Z W N) (ho : o < N)
    (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) (hsh : sh < W / 2) (h10 : s.gpr .r10 = B + BitVec.ofNat 32 (arr W a))
    (h1 : s.gpr .r1 = BitVec.ofNat 32 (4 * sh)) :
    WP isa (shiftDownBH o) s fun t => Ws t B Z W N ∧
      Outside (State.addr B) (arr W o) (4 * (W / 2 - sh)) s.mem t.mem ∧
      val32 t.mem (State.addr B) (arr W o) (W / 2 - sh) =
        val32 s.mem (State.addr B) (arr W a + 4 * sh) (W / 2 - sh) ∧
      Rest opRegs s t := by
  have := h.wle
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have da := arr_disj (w := W) hoa
  simp only [S] at fo fa da
  rw [shiftDownBH, WP.seq_iff]
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  have h2' : Ws s2 B Z W N := (h.of_upd u1 (by decide) (by decide) (by decide)).of_upd u2 (by decide) (by decide)
    (by decide)
  refine ptr_ok h2' (r := .r0) (by decide) (j := o) (by omega) fun s3 p3 r3 m3 h3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_lsr (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun x u6 => WP.block_nil ?_
  have hx : Ws x B Z W N :=
    (((h3.of_upd u4 (by decide) (by decide) (by decide)).of_upd u5 (by decide) (by decide) (by decide)).of_upd u6
      (by decide) (by decide) (by decide))
  have mx : x.mem = s.mem := u6.mem.trans (u5.mem.trans (u4.mem.trans (m3.trans (u2.mem.trans u1.mem))))
  have restX : Rest opRegs s x :=
    ((u1.rest (by simp)).trans ((u2.rest (by simp)).trans (r3.mono (by simp)))).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))
  have q10 : s1.gpr .r10 = B + BitVec.ofNat 32 (arr W a + 4 * sh) := by
    rw [u1.gpr, dpVal, h10, h1, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc]
  have p0 : x.gpr .r0 = B + BitVec.ofNat 32 (arr W o) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), p3]
  have p10 : x.gpr .r10 = B + BitVec.ofNat 32 (arr W a + 4 * sh) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide),
      u2.other _ (by decide), q10]
  have p12 : x.gpr .r12 = B + BitVec.ofNat 32 (arr W a + 4 * sh) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide), u2.gpr, q10]
  have plr : x.gpr .lr = BitVec.ofNat 32 (W / 2 - sh) := by
    rw [u6.other _ (by decide), u5.gpr, dpVal, u4.gpr, h3.r9, lsr1_val (by omega), u4.other _ (by decide),
      r3.gpr _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h1,
      VG.Proof.Rsa.Arm.KeyDiv.shr2_val (by omega), BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  have sc : SubCtx x B Z (arr W o) (arr W a + 4 * sh) (arr W a + 4 * sh) (W / 2 - sh) :=
    ⟨h.nowrap, by omega, by omega, by omega, by omega, by omega, by rw [restX.wr]; exact h.writable⟩
  refine WP.mono (copyWords_ok x sc (by omega) p0 p10 p12 plr) fun t inv => ?_
  have v := inv.value
  rw [mx, u6.gpr] at v
  refine ⟨hx.rest inv.rest, by simpa only [mx] using inv.outside, by simpa using v,
    restX.trans (inv.rest.mono (by simp))⟩

section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

theorem two_le_W (P : RP) : 2 ≤ P.W := by simp only [RP.W]; omega

/-- `halfKHN j k`, `r11 = 0`, for `[j]` below `2^(32 W / 2)`. -/
theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.halfKH_W {j k : Nat} (hk : 0 < k ∧ k < 32) (h : KS P σ A live AW liveW V ls s)
    (hv : Ws s P.B P.Z P.W 22) (hj : j ∈ liveW) (r11 : s.gpr .r11 = 0) (hl : ∀ i ∈ live, i / 2 ≠ j)
    (hb : AW j < 2 ^ (32 * (P.W / 2))) :
    WP isa (halfKHN j k) s fun t => KS P σ A live (upd AW j (AW j / 2 ^ k)) (j :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t := by
  have sz := h.sizes
  have hj22 := h.liveW_lt j hj
  have fo := fit_W sz hj22
  simp only [S] at fo
  have w2 := two_le_W P
  refine WP.mono (halfKHN_ok hk hv hj22 (by decide) w2 r11) fun t ⟨ht, O, v, r⟩ => ?_
  have kk : Keep P.B P.W [j] [] s.mem t.mem := Keep.of_arr (d := 0) (by simpa using O)
    (by have : S P.W = 4 * (P.W + 2) := rfl; have : P.W = 2 * P.w + 2 := rfl; omega) (List.mem_singleton_self j)
  refine ⟨h.write_W kk hj22 (by simp) (h.r8_of r) r.sp r.rd r.wr ?_ hl (by simp), ht, r⟩
  have hb' : num s.mem P.B P.W j < 2 ^ (32 * (P.W / 2 + 1)) := by
    rw [h.arrsW j hj]; exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega))
  rw [num_prefix_write (by omega) O (by omega) hb', v, h.prefix_val hj (by omega) hb]

end

section
variable {P : RP}

/-- `lr := W / 2`. -/
theorem lrH_ok {σ s : State} {A AW V : Nat → Nat} {L LW LS : List Nat} {rest : List Instr} {Q : State → Prop}
    (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.W 22)
    (k : ∀ t, KS P σ A L AW LW V LS t → Ws t P.B P.Z P.W 22 → t.gpr .lr = BitVec.ofNat 32 (P.W / 2) →
      Rest [.lr] s t → WP isa (.block rest) t Q) :
    WP isa (.block (lrH :: rest)) s Q := by
  have wl := hv.wle
  refine wp_mov (op2_lsr (by decide)) fun t u => ?_
  obtain ⟨ht, hvt⟩ := h.reg hv (u.rest (ws := [.lr]) (by simp)) u.mem
  exact k t ht hvt (by rw [u.gpr, hv.r9, lsr1_val (by omega)]) (u.rest (by simp))

/-- `copyH o a`, both below `2^(32 W / 2)`. -/
theorem copyH_vp {o a : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (ho : o < 22) (hoW : o ∈ LW) (ha : a ∈ LW) (hoa : o ≠ a) (hl : ∀ j ∈ L, j / 2 ≠ o)
    (hza : ∀ σ, E σ → AW σ a < 2 ^ (32 * (P.W / 2))) (hzo : ∀ σ, E σ → AW σ o < 2 ^ (32 * (P.W / 2)))
    (cert : DCert (copyH o a)) :
    VP (Dk P E A L AW LW V LS P.W 22) (copyH o a) (Dk P E A L (fun σ => upd (AW σ) o (AW σ a)) LW V LS P.W 22) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => by
    have w2 := two_le_W P
    rw [copyH, WP.seq_iff]
    refine lrH_ok h hv fun t ht hvt lr _ => WP.block_nil ?_
    refine WP.mono (ht.copyN_W hvt ho ha hoa hl (by omega) (by omega) lr (hza σ e)
      (by rw [ht.arrsW o hoW]; exact hzo σ e)) fun u ⟨hu, hvu, _⟩ => ⟨e, hu.mono (fun j hj => ⟨hj, rfl⟩)
        (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩), hvu⟩

/-- `selH o a b sl`, all three below `2^(32 W / 2)`. -/
theorem selH_vp {o a b sl : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (ho : o < 22) (hoW : o ∈ LW) (ha : a ∈ LW) (hb : b ∈ LW) (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ LS)
    (bit : ∀ σ, E σ → V σ sl ≤ 1) (hl : ∀ j ∈ L, j / 2 ≠ o)
    (hza : ∀ σ, E σ → AW σ a < 2 ^ (32 * (P.W / 2))) (hzb : ∀ σ, E σ → AW σ b < 2 ^ (32 * (P.W / 2)))
    (hzo : ∀ σ, E σ → AW σ o < 2 ^ (32 * (P.W / 2))) (cert : DCert (selH o a b sl)) :
    VP (Dk P E A L AW LW V LS P.W 22) (selH o a b sl)
      (Dk P E A L (fun σ => upd (AW σ) o (if V σ sl = 0 then AW σ a else AW σ b)) LW V LS P.W 22) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => by
    have w2 := two_le_W P
    rw [selH, WP.seq_iff]
    refine lrH_ok h hv fun t ht hvt lr _ => WP.block_nil ?_
    refine WP.mono (ht.selN_W hvt ho ha hb hoa hob hsl (bit σ e) hl (by omega) (by omega) lr (hza σ e) (hzb σ e)
      (by rw [ht.arrsW o hoW]; exact hzo σ e)) fun u ⟨hu, hvu, _⟩ => ⟨e, hu.mono (fun j hj => ⟨hj, rfl⟩)
        (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩), hvu⟩

/-- `halfKH j k`: `[j] := ⌊[j] / 2^k⌋`, `[j]` below `2^(32 W / 2)`, the slot `sK` cleared. -/
theorem halfKH_vp {j k : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hk : 0 < k ∧ k < 32) (hj : j ∈ LW) (hl : ∀ i ∈ L, i / 2 ≠ j) (hb : ∀ σ, E σ → AW σ j < 2 ^ (32 * (P.W / 2)))
    (cert : DCert (halfKH j k)) :
    VP (Dk P E A L AW LW V LS P.W 22) (halfKH j k)
      (Dk P E A L (fun σ => upd (AW σ) j (AW σ j / 2 ^ k)) LW (fun σ => upd (V σ) sK 0) (sK :: LS) P.W 22) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => by
    rw [halfKH, WP.seq_iff]
    refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
    obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r11]) (by simp)) u1.mem
    have z1 : (s1.gpr .r11).toNat = 0 := by rw [u1.gpr]; rfl
    refine h1.strSlot hv1 (d := sK) (r := .r11) (by decide) fun s2 h2 hv2 g2 _ => WP.block_nil ?_
    rw [z1] at h2
    refine WP.mono (h2.halfKH_W hk hv2 hj (by rw [g2, u1.gpr]) hl (hb σ e)) fun t ⟨ht, hvt, _⟩ =>
      ⟨e, ht.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨List.mem_cons_of_mem _ hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩), hvt⟩

/-- A masked stage over the root's words: `op` puts `F` into `[t1]`; then `[x]` and `[t2]` := `F` where the bit
at `sBit` is set, else `[x]`. -/
theorem selStageH_vp {x t1 t2 : Nat} {op : Prog isa} {L LW LS LS' : List Nat} {E : State → Prop}
    {A AW V V' : State → Nat → Nat} {F : State → Nat}
    (hx : x ∈ LW) (h1 : t1 ∈ LW) (h2 : t2 ∈ LW) (hx22 : x < 22) (ht2 : t2 < 22) (h1x : t1 ≠ x) (h2x : t2 ≠ x)
    (h12 : t2 ≠ t1) (hL : ∀ j ∈ L, j / 2 ≠ t2 ∧ j / 2 ≠ x) (hB : sBit ∈ LS') (bit : ∀ σ, E σ → V' σ sBit ≤ 1)
    (bx : ∀ σ, E σ → AW σ x < 2 ^ (32 * (P.W / 2))) (bF : ∀ σ, E σ → F σ < 2 ^ (32 * (P.W / 2)))
    (b2 : ∀ σ, E σ → AW σ t2 < 2 ^ (32 * (P.W / 2)))
    (hop : VP (Dk P E A L AW LW V LS P.W 22) op (Dk P E A L (fun σ => upd (AW σ) t1 (F σ)) LW V' LS' P.W 22))
    (cS : DCert (selH t2 x t1 sBit)) (cC : DCert (copyH x t2)) :
    VP (Dk P E A L AW LW V LS P.W 22) (selStageH op x t1 t2)
      (Dk P E A L (fun σ => upd (upd (upd (AW σ) t1 (F σ)) t2 (if V' σ sBit = 0 then AW σ x else F σ)) x
        (if V' σ sBit = 0 then AW σ x else F σ)) LW V' LS' P.W 22) := by
  simp only [selStageH, seqs]
  refine hop.seq ((selH_vp (o := t2) (a := x) (b := t1) (sl := sBit) ht2 h2 hx h1 h2x h12 hB bit
    (fun j hj => (hL j hj).1) (fun σ e => by rw [upd_ne _ _ (Ne.symm h1x)]; exact bx σ e)
    (fun σ e => by rw [upd_self]; exact bF σ e) (fun σ e => by rw [upd_ne _ _ h12]; exact b2 σ e) cS).seq ?_)
  refine (copyH_vp (o := x) (a := t2) hx22 hx h2 (Ne.symm h2x) (fun j hj => (hL j hj).2)
    (fun σ e => by
      rw [upd_self]; split
      · rw [upd_ne _ _ (Ne.symm h1x)]; exact bx σ e
      · rw [upd_self]; exact bF σ e)
    (fun σ e => by rw [upd_ne _ _ (Ne.symm h2x), upd_ne _ _ (Ne.symm h1x)]; exact bx σ e) cC).mono
    (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩)
      (fun d hd => ⟨hd, rfl⟩), hv⟩
  simp only [upd_self, upd_ne _ _ (Ne.symm h1x)]

/-- The root's bit stage `i`: `[wS]` shifted right by `2^i` bits where bit `i` of `t` (at `sTu`) is set;
`[wG]` and `[wF]` any values below `2^(32 W / 2)` before, and known after. -/
theorem rootBitStage_vp {i : Nat} (hi : i < 5) {L LW LS : List Nat} {E : State → Prop}
    {A AW V : State → Nat → Nat} {v t g f : State → Nat}
    (hS' : wS ∈ LW) (hG : wG ∈ LW) (hF : wF ∈ LW) (hL : ∀ j ∈ L, j / 2 ≠ wG ∧ j / 2 ≠ wF ∧ j / 2 ≠ wS)
    (hS : sTu ∈ LS) (vS : ∀ σ, E σ → V σ sTu = t σ) (bv : ∀ σ, E σ → v σ < 2 ^ (32 * (P.W / 2)))
    (bg : ∀ σ, E σ → g σ < 2 ^ (32 * (P.W / 2))) (bf : ∀ σ, E σ → f σ < 2 ^ (32 * (P.W / 2))) :
    VP (Dk P E A L (fun σ => upd (upd (upd (AW σ) wG (g σ)) wF (f σ)) wS (v σ / 2 ^ (t σ % 2 ^ i))) LW V LS
        P.W 22) (rootBitStage i)
      (Dk P E A L (fun σ => upd (upd (upd (AW σ) wG (v σ / 2 ^ (t σ % 2 ^ i) / 2 ^ (2 ^ i))) wF
          (v σ / 2 ^ (t σ % 2 ^ (i + 1)))) wS (v σ / 2 ^ (t σ % 2 ^ (i + 1)))) LW
        (fun σ => upd (upd (V σ) sBit (t σ / 2 ^ i % 2)) sK 0) (sK :: sBit :: LS) P.W 22) := by
  have p : 2 ^ i < 32 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (show i ≤ 4 by omega)) (by decide)
  have bx : ∀ σ, E σ → v σ / 2 ^ (t σ % 2 ^ i) < 2 ^ (32 * (P.W / 2)) := fun σ e =>
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (bv σ e)
  simp only [rootBitStage, seqs]
  refine VP.seq (G := Dk P E A L (fun σ => upd (upd (upd (AW σ) wG (g σ)) wF (f σ)) wS (v σ / 2 ^ (t σ % 2 ^ i)))
      LW (fun σ => upd (V σ) sBit (t σ / 2 ^ i % 2)) (sBit :: LS) P.W 22)
    (VP.dctx (bitToU_taint i hi) (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      WP.mono (bitTo_ok (by omega) hS h hv) fun y ⟨hy, hvy⟩ => ⟨e, by rwa [vS σ e] at hy, hvy⟩) ?_
  refine (copyH_vp (o := wG) (a := wS) (by decide) hG hS' (by decide) (fun j hj => (hL j hj).1)
    (fun σ e => by rw [upd_self]; exact bx σ e)
    (fun σ e => by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]; exact bg σ e) copyGSH_taint).seq ?_
  refine (selStageH_vp (x := wS) (t1 := wG) (t2 := wF) (F := fun σ => v σ / 2 ^ (t σ % 2 ^ i) / 2 ^ (2 ^ i))
    hS' hG hF (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun j hj => ⟨(hL j hj).2.1, (hL j hj).2.2⟩) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (fun σ _ => by simp only [upd_ne _ _ (show sBit ≠ sK by decide), upd_self]
                   exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    (fun σ e => by rw [upd_ne _ _ (by decide), upd_self]; exact bx σ e)
    (fun σ e => Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (bx σ e))
    (fun σ e => by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]; exact bf σ e)
    ((halfKH_vp (j := wG) (k := 2 ^ i) ⟨Nat.two_pow_pos _, p⟩ hG
      (fun j hj => (hL j hj).1) (fun σ e => by rw [upd_self]; exact bx σ e) (halfKHG_taint i hi)).mono
      (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩)
        (fun j hj => ⟨hj, by simp only [upd_self]⟩) (fun d hd => ⟨hd, rfl⟩), hv⟩)
    selFSGH_taint copySFH_taint).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩)
      (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩), hv⟩
  have hsel : (if t σ / 2 ^ i % 2 = 0 then v σ / 2 ^ (t σ % 2 ^ i) else v σ / 2 ^ (t σ % 2 ^ i) / 2 ^ (2 ^ i)) =
      v σ / 2 ^ (t σ % 2 ^ (i + 1)) := shift_sel_div _ _ _
  simp only [upd_ne _ _ (show sBit ≠ sK by decide), upd_self, upd_ne _ _ (show wS ≠ wG by decide), hsel]
  by_cases c1 : j = wS
  · subst c1; simp only [upd_self]
  · by_cases c2 : j = wF
    · subst c2; simp only [upd_self, upd_ne _ _ c1]
    · by_cases c3 : j = wG
      · subst c3; simp only [upd_self, upd_ne _ _ c1, upd_ne _ _ c2]
      · simp only [upd_ne _ _ c1, upd_ne _ _ c2, upd_ne _ _ c3]

end

/-! ### The root's word stages -/

/-- The root's word stages' count: `2^KWH ≥ W / 2`. -/
abbrev KWH (P : RP) : Nat := Nat.log2 (P.W / 2 - 1) + 1

section
variable {P : RP}

theorem two_le_H (sz : Sizes P) : 2 ≤ P.W / 2 := by
  have := sz.w6a; simp only [RP.W, RP.w]; omega

theorem kwh_pow (sz : Sizes P) {m : Nat} (hm : m < KWH P) : 2 ^ m < P.W / 2 := by
  have w2 := two_le_H sz
  have := Nat.log2_self_le (n := P.W / 2 - 1) (by omega)
  have := Nat.pow_le_pow_right (n := 2) (by decide) (show m ≤ Nat.log2 (P.W / 2 - 1) by simp only [KWH] at hm; omega)
  omega

theorem kwh_ge : P.W / 2 ≤ 2 ^ KWH P := by
  have := Nat.lt_log2_self (n := P.W / 2 - 1)
  simp only [KWH]; omega

theorem stageNextH_ok {m q : Nat} {LS : List Nat} {σ s : State} {A AW V : Nat → Nat} {L LW : List Nat}
    (hm : 2 ^ m < P.W / 2) (hT : sTk ∈ LS) (hW : sWs ∈ LS) (vT : V sTk = q / 2 ^ m) (vW : V sWs = 4 * 2 ^ m)
    (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.W 22) :
    WP isa (.block stageNextH) s fun t =>
      (KS P σ A L AW LW (upd (upd V sTk (q / 2 ^ (m + 1))) sWs (4 * 2 ^ (m + 1))) (sWs :: sTk :: LS) t ∧
        Ws t P.B P.Z P.W 22) ∧ t.z = decide (KWH P - (m + 1) = 0) := by
  have sz := h.sizes
  have Wl := sz.Wle
  have w2 := two_le_H sz
  have we : P.W = 2 * (P.W / 2) := by simp only [RP.W]; omega
  have p1 : 2 ^ (m + 1) ≤ P.W := by rw [Nat.pow_succ]; omega
  have b1 : q / 2 ^ m < 2 ^ 32 := by rw [← vT, ← h.sl sTk hT]; exact BitVec.isLt _
  unfold stageNextH
  refine h.ldrSlot hv (d := sTk) hT (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2.strSlot hv2 (d := sTk) (r := .r1) (by decide) fun s3 h3 hv3 g3 _ => ?_
  refine h3.ldrSlot hv3 (d := sWs) (by simp [hW]) (r := .r1) (by decide) fun s7 h7 hv7 u7 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s8 u8 => ?_
  obtain ⟨h8, hv8⟩ := h7.reg hv7 (u8.rest (ws := [.r1]) (by simp)) u8.mem
  refine h8.strSlot hv8 (d := sWs) (r := .r1) (by decide) fun s9 h9 hv9 g9 _ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s10 u10 => ?_
  obtain ⟨h10, hv10⟩ := h9.reg hv9 (u10.rest (ws := [.r1]) (by simp)) u10.mem
  refine wp_mov (op2_lsr (by decide)) fun s11 u11 => ?_
  obtain ⟨h11, hv11⟩ := h10.reg hv10 (u11.rest (ws := [.r1]) (by simp)) u11.mem
  refine wp_cmp (op2_imm (by decide)) fun t ut zt => WP.block_nil ?_
  obtain ⟨ht, hvt⟩ := h11.reg hv11 (ut.rest []) ut.mem
  have e2 : (s2.gpr .r1).toNat = q / 2 ^ (m + 1) := by rw [u2.gpr, u1.gpr]; exact halfSlot vT b1
  have e8 : (s8.gpr .r1).toNat = 4 * 2 ^ (m + 1) := by
    rw [u8.gpr, u7.gpr]
    simp only [upd_ne _ _ (show sWs ≠ sTk by decide), vW]
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_succ, Nat.pow_succ 2 m,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have r11v : s11.gpr .r1 = if 4 * 2 ^ (m + 1) < 4 * (P.W / 2) then 1 else 0 := by
    rw [u11.gpr, u10.gpr, dpVal, hv9.r9, g9]
    rw [show s8.gpr .r1 = BitVec.ofNat 32 (4 * 2 ^ (m + 1)) from BitVec.eq_of_toNat_eq (by
      rw [e8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])]
    rw [show BitVec.ofNat 32 P.W <<< 1 = BitVec.ofNat 32 (4 * (P.W / 2)) from BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (a := P.W) (by omega)]; omega)]
    exact sign_bit (by omega) (by omega)
  refine ⟨⟨ht.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨?_, ?_⟩), hvt⟩, ?_⟩
  · simp only [List.mem_cons] at hd ⊢; grind
  · rw [e8, e2]
  · rw [zt, r11v]
    have e : 4 * 2 ^ (m + 1) < 4 * (P.W / 2) ↔ m + 1 ≤ Nat.log2 (P.W / 2 - 1) := by
      rw [Nat.le_log2 (by omega)]; omega
    by_cases c : m + 1 ≤ Nat.log2 (P.W / 2 - 1)
    · simp only [e.mpr c, ↓reduceIte]
      have : ¬ KWH P - (m + 1) = 0 := by simp only [KWH]; omega
      simp only [this, decide_false]; rfl
    · simp only [show ¬ 4 * 2 ^ (m + 1) < 4 * (P.W / 2) from fun h => c (e.mp h), ↓reduceIte]
      have : KWH P - (m + 1) = 0 := by simp only [KWH]; omega
      simp only [this, decide_true]; rfl

/-- `shiftDownByH d o a`: `[o] := ⌊[a] / 2^(32 sh)⌋` for `4 sh` at `d`, both below `2^(32 W / 2)`. -/
theorem shiftDownByH_vp {d sh o a : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hsh : sh < P.W / 2) (ho : o < 22) (hoW : o ∈ LW) (ha : a ∈ LW) (hoa : o ≠ a) (hz : wZ ∈ LW) (hoz : o ≠ wZ)
    (hL : ∀ j ∈ L, j / 2 ≠ o) (hS : d ∈ LS) (z0 : ∀ σ, E σ → AW σ wZ = 0) (vS : ∀ σ, E σ → V σ d = 4 * sh)
    (ba : ∀ σ, E σ → AW σ a < 2 ^ (32 * (P.W / 2))) (bo : ∀ σ, E σ → AW σ o < 2 ^ (32 * (P.W / 2)))
    (certC : DCert (copyH o wZ)) (certA : DCert (.block (ptr .r10 a ++ ([.ldr .r1 .r8 d] : List Instr))))
    (certB : ShiftCert .r10 (shiftDownBH o)) :
    VP (Dk P E A L AW LW V LS P.W 22) (shiftDownByH d o a)
      (Dk P E A L (fun σ => upd (AW σ) o (AW σ a / 2 ^ (32 * sh))) LW V LS P.W 22) := by
  simp only [shiftDownByH, seqs]
  refine VP.seq (G := Dk P E A L (fun σ => upd (AW σ) o 0) LW V LS P.W 22)
    ((copyH_vp (o := o) (a := wZ) ho hoW hz hoz hL (fun σ e => by rw [z0 σ e]; exact Nat.two_pow_pos _) bo
      certC).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, by simpa only [z0 σ e] using h, hv⟩) ?_
  refine VP.seq (G := fun σ t => Dk P E A L (fun σ => upd (AW σ) o 0) LW V LS P.W 22 σ t ∧
      t.gpr .r10 = P.B + BitVec.ofNat 32 (arr P.W a) ∧ t.gpr .r1 = BitVec.ofNat 32 (4 * sh))
    (VP.dctx certA (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_)
    (VP.taint _ certB (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨e, h, hv⟩, p10, p1⟩ => ?_)
  · have ha22 := h.liveW_lt a ha
    refine ptr_ok hv (r := .r10) (by decide) (j := a) (by omega) fun s1 p1 r1 m1 hv1 => ?_
    have h1 := h.of_rest r1 m1 (by decide)
    refine h1.ldrSlot hv1 (d := d) hS (r := .r1) (by decide) fun t ht hvt U => WP.block_nil ⟨⟨e, ht, hvt⟩, ?_, ?_⟩
    · rw [U.other _ (by decide), p1]
    · rw [U.gpr, vS σ e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
    · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
  · have sz := h.sizes
    have Wl := sz.Wle
    have ha22 := h.liveW_lt a ha
    refine WP.mono (shiftDownBH_ok hv ho ha22 (by decide) hoa hsh p10 p1) fun t ⟨hvt, O, V', R⟩ =>
      ⟨e, ?_, hvt⟩
    have fo := fit_W sz ho
    have fa := fit_W sz ha22
    simp only [S] at fo fa
    have k : Keep P.B P.W [o] [] s.mem t.mem := Keep.of_arr (d := 0) (by simpa using O)
      (by have : P.W = 2 * P.w + 2 := rfl; simp only [S]; omega) (by simp)
    have v0 := h.arrsW o hoW
    simp only [upd_self] at v0
    have va := h.arrsW a ha
    simp only [upd_ne _ _ (Ne.symm hoa)] at va
    -- `[a]` below `2^(32 W / 2)`: its words from `sh` are those below `W / 2`
    have hi : val32 s.mem (State.addr P.B) (arr P.W a + 4 * (P.W / 2)) (P.W - P.W / 2) = 0 := by
      have e1 := numW_at s.mem P.B P.W a (P.W / 2) (by omega)
      have := ba σ e
      rw [← va] at this
      rcases Nat.eq_zero_or_pos (val32 s.mem (State.addr P.B) (arr P.W a + 4 * (P.W / 2)) (P.W - P.W / 2))
        with c | c
      · exact c
      · have := Nat.mul_le_mul_left (2 ^ (32 * (P.W / 2))) c; omega
    have ea : AW σ a / 2 ^ (32 * sh) = val32 s.mem (State.addr P.B) (arr P.W a + 4 * sh) (P.W / 2 - sh) := by
      rw [← va, numW_at s.mem P.B P.W a (P.W / 2) (by omega), hi, Nat.mul_zero, Nat.add_zero,
        show P.W / 2 = sh + (P.W / 2 - sh) by omega, val32_append, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (val32_lt _ _ _ _), Nat.zero_add, Nat.add_sub_cancel_left]
    have ev' : num t.mem P.B P.W o = AW σ a / 2 ^ (32 * sh) := by
      rw [num_prefix_write (n := P.W / 2 - sh) (by omega) O (by omega) (by rw [v0]; exact Nat.two_pow_pos _), V',
        ea]
    have h' := h.write_W k ho (by simp) (h.r8_of R) R.sp R.rd R.wr ev' hL (by simp)
    refine h'.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
    simp only [upd]; split <;> rfl

/-- The root's word stage `m`: `[wS]` shifted down by `2^m` words where bit `m` of `q` is set; `[wG]` and `[wF]`
any values below `2^(32 W / 2)` before, and known after. -/
theorem rootWordStage_vp {m : Nat} (hm : m < KWH P) {L LW LS0 : List Nat} {E : State → Prop}
    {A AW0 V0 : State → Nat → Nat} {v c q g f : State → Nat}
    (hS : wS ∈ LW) (hG : wG ∈ LW) (hF : wF ∈ LW) (hz : wZ ∈ LW) (z0 : ∀ σ, E σ → AW0 σ wZ = 0)
    (hL : ∀ j ∈ L, j / 2 ≠ wG ∧ j / 2 ≠ wF ∧ j / 2 ≠ wS) (hLS : ∀ d ∈ LS0, d ≠ sBit ∧ d ≠ sTk ∧ d ≠ sWs)
    (bv : ∀ σ, E σ → v σ < 2 ^ (32 * (P.W / 2)))
    (bg : ∀ σ, E σ → g σ < 2 ^ (32 * (P.W / 2))) (bf : ∀ σ, E σ → f σ < 2 ^ (32 * (P.W / 2))) :
    VP (Dk P E A L (fun σ => upd (upd (upd (AW0 σ) wG (g σ)) wF (f σ)) wS (v σ / 2 ^ (c σ + 32 * (q σ % 2 ^ m))))
        LW (fun σ => WSV (V0 σ) (q σ) m) (LSS LS0) P.W 22)
      rootWordStage
      (fun σ s => Dk P E A L (fun σ => upd (upd (upd (AW0 σ) wG (v σ / 2 ^ (c σ + 32 * (q σ % 2 ^ m)) /
          2 ^ (32 * 2 ^ m))) wF (v σ / 2 ^ (c σ + 32 * (q σ % 2 ^ (m + 1))))) wS
          (v σ / 2 ^ (c σ + 32 * (q σ % 2 ^ (m + 1))))) LW
        (fun σ => WSV (V0 σ) (q σ) (m + 1)) (LSS LS0) P.W 22 σ s ∧ s.z = decide (KWH P - (m + 1) = 0)) :=
  VP.of_imp (p := 2 ^ m < P.W / 2) (fun _ _ h => kwh_pow h.2.1.sizes hm) fun hm' => by
    have zG : wZ ≠ wG := by decide
    have zF : wZ ≠ wF := by decide
    have zS : wZ ≠ wS := by decide
    let x := fun σ => v σ / 2 ^ (c σ + 32 * (q σ % 2 ^ m))
    have bx : ∀ σ, E σ → x σ < 2 ^ (32 * (P.W / 2)) := fun σ e => Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (bv σ e)
    simp only [rootWordStage, seqs]
    refine VP.seq (G := Dk P E A L (fun σ => upd (upd (upd (AW0 σ) wG (g σ)) wF (f σ)) wS (x σ)) LW
        (fun σ => upd (WSV (V0 σ) (q σ) m) sBit (q σ / 2 ^ m % 2)) (sBit :: LSS LS0) P.W 22)
      (VP.dctx bitToTk_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
        WP.mono (bitTo_ok (i := 0) (by omega) (by simp) h hv) fun y ⟨hy, hvy⟩ =>
          ⟨e, by
            have e1 : WSV (V0 σ) (q σ) m sTk = q σ / 2 ^ m := by simp only [WSV]; rd_up
            simp only [e1, Nat.pow_zero, Nat.div_one] at hy; exact hy, hvy⟩) ?_
    refine (selStageH_vp (x := wS) (t1 := wG) (t2 := wF) (F := fun σ => x σ / 2 ^ (32 * 2 ^ m))
      hS hG hF (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun j hj => ⟨(hL j hj).2.1, (hL j hj).2.2⟩) (List.mem_cons_self ..)
      (fun σ _ => by simp only [upd_self]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
      (fun σ e => by rw [upd_self]; exact bx σ e)
      (fun σ e => Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (bx σ e))
      (fun σ e => by rw [upd_ne _ _ (by decide), upd_self]; exact bf σ e)
      ((shiftDownByH_vp (d := sWs) (sh := 2 ^ m) (o := wG) (a := wS) hm' (by decide) hG hS (by decide) hz (by decide)
        (fun j hj => (hL j hj).1) (by simp)
        (fun σ e => by rw [upd_ne _ _ zS, upd_ne _ _ zF, upd_ne _ _ zG]; exact z0 σ e)
        (fun σ _ => by simp only [upd_ne _ _ (show sWs ≠ sBit by decide), WSV]; rd_up)
        (fun σ e => by rw [upd_self]; exact bx σ e)
        (fun σ e => by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]; exact bg σ e)
        copyGZH_taint ptrS_taint downGH_taint).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ =>
          ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, by simp only [upd_self]⟩) (fun d hd => ⟨hd, rfl⟩), hv⟩)
      selFSGH_taint copySFH_taint).seq ?_
    refine VP.dctx stageNextH_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      WP.mono (stageNextH_ok (q := q σ) hm' (by simp) (by simp) (by simp only [WSV]; rd_up)
        (by simp only [WSV]; rd_up) h hv)
        fun t ⟨⟨ht, hvt⟩, z⟩ => ⟨⟨e, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨?_, ?_⟩),
          hvt⟩, z⟩
    · have hsel : (if q σ / 2 ^ m % 2 = 0 then x σ else x σ / 2 ^ (32 * 2 ^ m)) =
          v σ / 2 ^ (c σ + 32 * (q σ % 2 ^ (m + 1))) := shift_sel_divW _ _ _ _
      simp only [upd_self, hsel]
      by_cases c1 : j = wS
      · subst c1; simp only [upd_self]
      · by_cases c2 : j = wF
        · subst c2; simp only [upd_self, upd_ne _ _ c1]
        · by_cases c3 : j = wG
          · subst c3; simp only [upd_self, upd_ne _ _ c1, upd_ne _ _ c2, x]
          · simp only [upd_ne _ _ c1, upd_ne _ _ c2, upd_ne _ _ c3]
    · simp only [LSS, List.mem_cons] at hd ⊢; grind
    · simp only [WSV]
      simp only [LSS, List.mem_cons] at hd
      rcases hd with rfl | rfl | hd
      · rd_up
      · rd_up
      · obtain ⟨a1, a2, a3⟩ := hLS d hd
        simp only [upd_ne _ _ a1, upd_ne _ _ a2, upd_ne _ _ a3]

end

/-! ## The leading zeros -/

/-- The leading zeros of `x` among the top `p` of `N` bits (`p` if they are all zero). -/
def lzc (x N : Nat) : Nat → Nat
  | 0 => 0
  | p + 1 => if x / 2 ^ (N - (p + 1)) = 0 then p + 1 else lzc x N p

theorem lzc_zero {x N p : Nat} (h : x / 2 ^ (N - p) = 0) : lzc x N p = p := by
  cases p with
  | zero => rfl
  | succ p => simp only [lzc, h, ↓reduceIte]

theorem lzc_le (x N : Nat) : ∀ p, lzc x N p ≤ p
  | 0 => Nat.le_refl _
  | p + 1 => by
    simp only [lzc]; split
    · exact Nat.le_refl _
    · have := lzc_le x N p; omega

theorem sub_ofNat_eq (B : BitVec 32) {a c : Nat} (hc : c ≤ a) (hc' : c < 2 ^ 32) :
    B + BitVec.ofNat 32 a - BitVec.ofNat 32 c = B + BitVec.ofNat 32 (a - c) := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
    BitVec.ofNat_sub_ofNat_of_le _ _ hc' hc]

/-- A step of the top bit: `x / 2^e` from its halving and its bit. -/
theorem div_pow_bit (x e : Nat) : x / 2 ^ e = 2 * (x / 2 ^ (e + 1)) + x / 2 ^ e % 2 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

/-- `r6` after `k` doublings of a word `a`: its top bit is bit `31 - k` of `a`. -/
theorem top_bit {a k : Nat} (hk : k < 32) :
    (BitVec.ofNat 32 (a % 2 ^ (32 - k) * 2 ^ k) >>> 31) = BitVec.ofNat 32 (a / 2 ^ (31 - k) % 2) := by
  apply BitVec.eq_of_toNat_eq
  have l : a % 2 ^ (32 - k) * 2 ^ k < 2 ^ 32 := by
    have := Nat.mod_lt a (Nat.two_pow_pos (32 - k))
    calc a % 2 ^ (32 - k) * 2 ^ k < 2 ^ (32 - k) * 2 ^ k := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
      _ = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt l,
    Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 31 = 2 ^ (31 - k) * 2 ^ k by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _), show 32 - k = (31 - k) + 1 by omega, Nat.pow_succ,
    Nat.mod_mul_right_div_self]
  exact (Nat.mod_eq_of_lt (by have := Nat.mod_lt (a / 2 ^ (31 - k)) (show 0 < 2 by decide); omega)).symm

theorem shl_word {a k : Nat} (hk : k < 32) :
    (BitVec.ofNat 32 (a % 2 ^ (32 - k) * 2 ^ k) <<< 1) = BitVec.ofNat 32 (a % 2 ^ (32 - (k + 1)) * 2 ^ (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have l : ∀ j, j ≤ 32 → a % 2 ^ (32 - j) * 2 ^ j < 2 ^ 32 := fun j hj => by
    have := Nat.mod_lt a (Nat.two_pow_pos (32 - j))
    calc a % 2 ^ (32 - j) * 2 ^ j < 2 ^ (32 - j) * 2 ^ j := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
      _ = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (l k (by omega)),
    Nat.mod_eq_of_lt (l (k + 1) (by omega)), Nat.shiftLeft_eq, Nat.mul_assoc, ← Nat.pow_succ,
    show (2 : Nat) ^ 32 = 2 ^ (32 - (k + 1)) * 2 ^ (k + 1) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_mod_mul_right, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

section
variable {P : RP}

/-- Bit `k` of word `i` from the top of `x` (`a`, its word `W - 1 - i` and above): `r6` the word's bits
left, shifted to the top, `r4` the leading zeros above and `r5` whether a bit above is set. -/
abbrev LZB (P : RP) (j x i k : Nat) (s : State) : Prop :=
  s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W j + 4 * (P.W - i) - 8) ∧ s.gpr .lr = BitVec.ofNat 32 (P.W - i) ∧
    s.gpr .r12 = BitVec.ofNat 32 (32 - k) ∧
    s.gpr .r6 = BitVec.ofNat 32 (x / 2 ^ (32 * (P.W - 1 - i)) % 2 ^ (32 - k) * 2 ^ k) ∧
    s.gpr .r4 = BitVec.ofNat 32 (lzc x (32 * P.W) (32 * i + k)) ∧
    s.gpr .r5 = BitVec.ofNat 32 (if x / 2 ^ (32 * P.W - (32 * i + k)) = 0 then 0 else 1)

theorem clzBit_ok {j x i k : Nat} {σ s : State} {A AW V : Nat → Nat} {L LW LS : List Nat} (hk : k < 32)
    (hi : i < P.W) (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.W 22) (c : LZB P j x i k s) :
    WP isa (.block clzBit) s fun t => (KS P σ A L AW LW V LS t ∧ Ws t P.B P.Z P.W 22 ∧ LZB P j x i (k + 1) t) ∧
      t.z = decide (32 - (k + 1) = 0) := by
  obtain ⟨p0, plr, p12, p6, p4, p5⟩ := c
  unfold clzBit
  refine wp_mov (op2_lsr (by decide)) fun s1 u1 => ?_
  obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r5]) (by simp)) u2.mem
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r4]) (by simp)) u4.mem
  refine wp_mov (op2_lsl (by decide)) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r6]) (by simp)) u5.mem
  refine wp_subs (op2_imm (by decide)) fun t ut zt => WP.block_nil ?_
  obtain ⟨ht, hvt⟩ := h5.reg hv5 (ut.rest (ws := [.r12]) (by simp)) ut.mem
  set p := 32 * i + k with hp
  set N := 32 * P.W with hN
  have pN : p < N := by omega
  have eN : N - (p + 1) = 32 * (P.W - 1 - i) + (31 - k) := by omega
  have bl : x / 2 ^ (N - (p + 1)) % 2 < 2 := Nat.mod_lt _ (by decide)
  have dv := div_pow_bit x (N - (p + 1))
  rw [show N - (p + 1) + 1 = N - p by omega] at dv
  have r1v : s1.gpr .r1 = BitVec.ofNat 32 (x / 2 ^ (N - (p + 1)) % 2) := by
    rw [u1.gpr, p6, top_bit hk, Nat.div_div_eq_div_mul, ← Nat.pow_add, eN]
  have c5 : (if x / 2 ^ (N - (p + 1)) = 0 then 0 else 1) = (if (if x / 2 ^ (N - p) = 0 then 0 else 1) = 0 ∧
      x / 2 ^ (N - (p + 1)) % 2 = 0 then 0 else 1) := by
    by_cases a : x / 2 ^ (N - p) = 0
    · by_cases b : x / 2 ^ (N - (p + 1)) % 2 = 0
      · have : x / 2 ^ (N - (p + 1)) = 0 := by omega
        simp only [this, a, ↓reduceIte, and_self]
      · have : x / 2 ^ (N - (p + 1)) ≠ 0 := by omega
        simp only [this, a, b, ↓reduceIte, and_false]
    · have : x / 2 ^ (N - (p + 1)) ≠ 0 := by omega
      simp only [this, a, ↓reduceIte, Nat.one_ne_zero, false_and]
  have r5v : s2.gpr .r5 = BitVec.ofNat 32 (if x / 2 ^ (N - (p + 1)) = 0 then 0 else 1) := by
    rw [u2.gpr, dpVal, u1.other .r5 (by decide), p5, r1v, bit_or _ (by split <;> omega) _ bl, c5]
  have r1v' : s3.gpr .r1 = BitVec.ofNat 32 (1 - if x / 2 ^ (N - (p + 1)) = 0 then 0 else 1) := by
    rw [u3.gpr, dpVal, r5v, bit_eor _ (by split <;> omega)]
  refine ⟨⟨ht, hvt, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [ut.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), p0]
  · rw [ut.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), plr]
  · rw [ut.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), p12, (cnt_sub (by omega) (by omega)).1]; congr 1
  · rw [ut.other _ (by decide), u5.gpr, u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), p6, shl_word hk]
  · rw [ut.other _ (by decide), u5.other _ (by decide), u4.gpr, dpVal, u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), p4, r1v', ← BitVec.ofNat_add,
      show 32 * i + (k + 1) = p + 1 by omega]
    congr 1
    simp only [lzc, ← hN]
    by_cases a : x / 2 ^ (N - (p + 1)) = 0
    · have a' : x / 2 ^ (N - p) = 0 := by omega
      simp only [a, ↓reduceIte, lzc_zero a', Nat.sub_zero]
    · simp only [a, ↓reduceIte, Nat.sub_self, Nat.add_zero]
  · rw [ut.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), r5v,
      show 32 * i + (k + 1) = p + 1 by omega]
  · rw [zt, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), p12, (cnt_sub (by omega) (by omega)).1, (cnt_sub (by omega) (by omega)).2]
    congr 1

end

section
variable {P : RP}

/-- Before word `i` from the top of the leading zeros of `x`. -/
abbrev LZO (P : RP) (j x i : Nat) (s : State) : Prop :=
  s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W j + 4 * (P.W - i) - 4) ∧ s.gpr .lr = BitVec.ofNat 32 (P.W - i) ∧
    s.gpr .r4 = BitVec.ofNat 32 (lzc x (32 * P.W) (32 * i)) ∧
    s.gpr .r5 = BitVec.ofNat 32 (if x / 2 ^ (32 * P.W - 32 * i) = 0 then 0 else 1)

theorem clzWord_ok {j i : Nat} {σ s : State} {A AW V : Nat → Nat} {L LW LS : List Nat} (hj : j ∈ LW)
    (hi : i < P.W) (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.W 22) (c : LZO P j (AW j) i s) :
    WP isa clzWord s fun t => (KS P σ A L AW LW V LS t ∧ Ws t P.B P.Z P.W 22 ∧ LZO P j (AW j) (i + 1) t) ∧
      t.z = decide (P.W - (i + 1) = 0) := by
  obtain ⟨p0, plr, p4, p5⟩ := c
  have sz := h.sizes
  have Wl := sz.Wle
  have j22 := h.liveW_lt j hj
  have fj := fit_W sz j22
  have fjZ := fitZ_W sz j22
  simp only [S] at fj fjZ
  have a8 : 8 ≤ arr P.W j := by simp only [arr, hdr]; omega
  have nw := hv.nowrap
  have dig : (s.mem.readW (off (State.addr P.B) (arr P.W j + 4 * (P.W - 1 - i))) 32).toNat =
      AW j / 2 ^ (32 * (P.W - 1 - i)) % 2 ^ 32 := by
    show w32 s.mem (State.addr P.B) (arr P.W j + 4 * (P.W - 1 - i)) = _
    have := h.arrsW j hj
    simp only [num] at this
    rw [w32_digit _ _ _ (show P.W - 1 - i < P.W by omega), this]
  have e0 : arr P.W j + 4 * (P.W - i) - 4 = arr P.W j + 4 * (P.W - 1 - i) := by omega
  simp only [clzWord, seqs]
  refine WP.seq ?_
  refine wp_ldr (by decide) (by rw [p0, BitVec.add_zero, e0, hv.addr (by omega)]) (hv.read (by omega)) fun s1 u1 => ?_
  obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r6]) (by simp)) u1.mem
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r12]) (by simp)) u3.mem
  refine WP.block_nil ?_
  refine WP.seq (WP.mono (wp_count (K := 32) (I := fun k t => KS P σ A L AW LW V LS t ∧ Ws t P.B P.Z P.W 22 ∧
    LZB P j (AW j) i k t) (by decide) (fun k hk t ⟨ht, hvt, ct⟩ => clzBit_ok hk hi ht hvt ct)
    ⟨h3, hv3, ?_, ?_, ?_, ?_, ?_, ?_⟩) ?_)
  · rw [u3.other _ (by decide), u2.gpr, dpVal, u1.other _ (by decide), p0,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_ofNat_eq _ (by omega) (by decide)]
    congr 2
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), plr]
  · rw [u3.gpr]; rfl
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, Nat.sub_zero, Nat.pow_zero, Nat.mul_one]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, dig, Nat.mod_mod]
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), p4, Nat.add_zero]
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), p5, Nat.add_zero]
  intro t ⟨ht, hvt, q0, qlr, _, _, q4, q5⟩
  refine wp_subs (op2_imm (by decide)) fun t' ut zt => WP.block_nil ?_
  obtain ⟨ht', hvt'⟩ := ht.reg hvt (ut.rest (ws := [.lr]) (by simp)) ut.mem
  refine ⟨⟨ht', hvt', ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [ut.other _ (by decide), q0]; congr 2; omega
  · rw [ut.gpr, qlr, (cnt_sub (by omega) (by omega)).1]; congr 1
  · rw [ut.other _ (by decide), q4, show 32 * i + 32 = 32 * (i + 1) by omega]
  · rw [ut.other _ (by decide), q5, show 32 * i + 32 = 32 * (i + 1) by omega]
  · rw [zt, qlr, (cnt_sub (by omega) (by omega)).1, (cnt_sub (by omega) (by omega)).2]; congr 1

/-- `lzW j d`: the leading zeros of `[j]` (wide, `32 W` for zero) at the slot `d`. -/
theorem lzW_vp {j d : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat} (hj : j ∈ LW)
    (hd : SlotOk d) (cert : DCert (lzW j d)) :
    VP (Dk P E A L AW LW V LS P.W 22) (lzW j d)
      (Dk P E A L AW LW (fun σ => upd (V σ) d (lzc (AW σ j) (32 * P.W) (32 * P.W))) (d :: LS) P.W 22) := by
  refine VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  have sz := h.sizes
  have Wl := sz.Wle
  have pos : 0 < P.W := by simp only [RP.W]; omega
  have j22 := h.liveW_lt j hj
  have fj := fitZ_W sz j22
  have nw := hv.nowrap
  simp only [S] at fj
  simp only [lzW, seqs]
  refine WP.seq ?_
  refine ptr_ok hv (r := .r0) (by decide) (j := j) (by omega) fun s1 p1 r1 m1 hv1 => ?_
  have h1 := h.of_rest r1 m1 (by decide)
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.lr]) (by simp)) u4.mem
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r4]) (by simp)) u5.mem
  refine wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r5]) (by simp)) u6.mem
  refine WP.block_nil ?_
  refine WP.seq (WP.mono (wp_count (K := P.W) (I := fun i t => KS P σ (A σ) L (AW σ) LW (V σ) LS t ∧
    Ws t P.B P.Z P.W 22 ∧ LZO P j (AW σ j) i t) pos (fun i hi t ⟨ht, hvt, ct⟩ => clzWord_ok hj hi ht hvt ct)
    ⟨h6, hv6, ?_, ?_, ?_, ?_⟩) ?_)
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.gpr, dpVal,
      p1, hv1.r7, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc, show (12 : BitVec 32) = BitVec.ofNat 32 12 from rfl,
      sub_ofNat_eq _ (by simp only [S]; omega) (by decide)]
    congr 2
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, hv3.r9, Nat.sub_zero]
  · rw [u6.other _ (by decide), u5.gpr, Nat.mul_zero]; rfl
  · rw [u6.gpr, Nat.mul_zero, Nat.sub_zero, Nat.div_eq_of_lt (h.lt_W hj)]; rfl
  intro t ⟨ht, hvt, _, _, q4, _⟩
  refine ht.strSlot hvt (d := d) (r := .r4) hd fun u hu hvu _ _ => WP.block_nil ⟨e, ?_, hvu⟩
  rw [q4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := lzc_le (AW σ j) (32 * P.W) (32 * P.W); omega)] at hu
  exact hu

end

/-! ## The first digit's root, a pair of bits at a time -/

theorem shl2_or (x y : BitVec 32) :
    x <<< 2 ||| y >>> 30 = BitVec.ofNat 32 (x.toNat * 4 % 2 ^ 32 + y.toNat / 2 ^ 30) := by
  apply BitVec.eq_of_toNat_eq
  have hb : y.toNat >>> 30 < 2 ^ 2 := by rw [Nat.shiftRight_eq_div_pow]; have := y.isLt; omega
  have ha : x.toNat <<< 2 % 2 ^ 32 = 2 ^ 2 * (x.toNat % 2 ^ 30) := by rw [Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, ha, ← Nat.two_pow_add_eq_or_of_lt hb,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := y.isLt; omega

theorem shl2_or1 (x : BitVec 32) : x <<< 2 ||| 1 = BitVec.ofNat 32 (x.toNat * 4 % 2 ^ 32 + 1) := by
  apply BitVec.eq_of_toNat_eq
  have hb : (1 : BitVec 32).toNat < 2 ^ 2 := by decide
  have ha : x.toNat <<< 2 % 2 ^ 32 = 2 ^ 2 * (x.toNat % 2 ^ 30) := by rw [Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, ha, ← Nat.two_pow_add_eq_or_of_lt hb, BitVec.toNat_ofNat]
  have : (1 : BitVec 32).toNat = 1 := rfl
  omega

/-- A 64-bit difference `Y - C` by words, its borrow from `subs`'s carry: the high word's sign, and the
difference where it is not negative. -/
theorem sub64_sign (y4 y5 h0 c6 : BitVec 32) (hY : y4.toNat * 2 ^ 32 + y5.toNat < 2 ^ 63)
    (hC : h0.toNat * 2 ^ 32 + c6.toNat < 2 ^ 63) :
    (y4 + (0 + 0 + bif decide (c6.toNat ≤ y5.toNat) then 1 else 0) - h0 - 1) >>> 31 =
      BitVec.ofNat 32 (if y4.toNat * 2 ^ 32 + y5.toNat < h0.toNat * 2 ^ 32 + c6.toNat then 1 else 0) ∧
    (¬ y4.toNat * 2 ^ 32 + y5.toNat < h0.toNat * 2 ^ 32 + c6.toNat →
      (y4 + (0 + 0 + bif decide (c6.toNat ≤ y5.toNat) then 1 else 0) - h0 - 1).toNat * 2 ^ 32 + (y5 - c6).toNat =
        y4.toNat * 2 ^ 32 + y5.toNat - (h0.toNat * 2 ^ 32 + c6.toNat)) := by
  have l4 := y4.isLt; have l5 := y5.isLt; have l0 := h0.isLt; have l6 := c6.isLt
  have eb : (0 + 0 + bif decide (c6.toNat ≤ y5.toNat) then (1 : BitVec 32) else 0) =
      bif decide (c6.toNat ≤ y5.toNat) then 1 else 0 := by simp
  have hb := VG.Proof.Rsa.Arm.KeyDiv.bit_toNat (decide (c6.toNat ≤ y5.toNat))
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [eb]
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add,
      hb, e1, BitVec.toNat_ofNat]
    by_cases c : c6.toNat ≤ y5.toNat <;>
      by_cases d : y4.toNat * 2 ^ 32 + y5.toNat < h0.toNat * 2 ^ 32 + c6.toNat <;>
      simp only [c, d, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;> omega
  · intro hn
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add, hb, e1, BitVec.toNat_sub]
    by_cases c : c6.toNat ≤ y5.toNat <;> simp only [c, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      omega

/-- A select by the mask `b - 1` of a bit `b`. -/
theorem sel_bit (x y : BitVec 32) (b : Nat) (hb : b < 2) :
    x ^^^ ((x ^^^ y) &&& (BitVec.ofNat 32 b - 1)) = if b = 1 then x else y := by
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · rw [show BitVec.ofNat 32 0 - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]; rfl
  · rw [show BitVec.ofNat 32 1 - 1 = 0#32 by decide, BitVec.and_zero, BitVec.xor_zero]; rfl

open VG.Proof.X25519.Arm (Rest) in
theorem isqBit_ok {s : State} {a1 a2 sv rh rl n : Nat} (g1 : (s.gpr .r1).toNat = a1) (g2 : (s.gpr .r2).toNat = a2)
    (g3 : (s.gpr .r3).toNat = sv) (g4 : (s.gpr .r4).toNat = rh) (g5 : (s.gpr .r5).toNat = rl)
    (glr : (s.gpr .lr).toNat = n) (hs : sv < 2 ^ 31) (hR : rh * 2 ^ 32 + rl ≤ 2 * sv) (hn : 1 ≤ n) :
    WP isa (.block isqBit) s fun t =>
      ((t.gpr .r1).toNat = a1 * 4 % 2 ^ 32 + a2 / 2 ^ 30 ∧ (t.gpr .r2).toNat = a2 * 4 % 2 ^ 32 ∧
        (t.gpr .r3).toNat = 2 * sv + (if 4 * sv + 1 ≤ 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30 then 1 else 0) ∧
        (t.gpr .r4).toNat * 2 ^ 32 + (t.gpr .r5).toNat = 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30 -
          (if 4 * sv + 1 ≤ 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30 then 4 * sv + 1 else 0) ∧
        (t.gpr .lr).toNat = n - 1 ∧ t.z = decide (n - 1 = 0) ∧ t.mem = s.mem) ∧
      Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr] s t := by
  refine WP.keep _ ?_ (by decide)
  have la1 : a1 < 2 ^ 32 := by rw [← g1]; exact (s.gpr .r1).isLt
  have la2 : a2 < 2 ^ 32 := by rw [← g2]; exact (s.gpr .r2).isLt
  have llr : n < 2 ^ 32 := by rw [← glr]; exact (s.gpr .lr).isLt
  have elr : s.gpr .lr = BitVec.ofNat 32 n := by rw [← glr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold isqBit
  krun [shl2_or, shl2_or1]
  generalize ey4 : BitVec.ofNat 32 ((s.gpr .r4).toNat * 4 % 2 ^ 32 + (s.gpr .r5).toNat / 2 ^ 30) = y4
  generalize ey5 : BitVec.ofNat 32 ((s.gpr .r5).toNat * 4 % 2 ^ 32 + (s.gpr .r1).toNat / 2 ^ 30) = y5
  generalize ec6 : BitVec.ofNat 32 ((s.gpr .r3).toNat * 4 % 2 ^ 32 + 1) = c6
  generalize eh0 : s.gpr .r3 >>> 30 = h0
  have v4 : y4.toNat = rh * 4 % 2 ^ 32 + rl / 2 ^ 30 := by
    rw [← ey4, BitVec.toNat_ofNat, g4, g5]; omega
  have v5 : y5.toNat = rl * 4 % 2 ^ 32 + a1 / 2 ^ 30 := by
    rw [← ey5, BitVec.toNat_ofNat, g5, g1]; omega
  have v6 : c6.toNat = sv * 4 % 2 ^ 32 + 1 := by rw [← ec6, BitVec.toNat_ofNat, g3]; omega
  have v0 : h0.toNat = sv / 2 ^ 30 := by rw [← eh0, BitVec.toNat_ushiftRight, g3, Nat.shiftRight_eq_div_pow]
  have eY : y4.toNat * 2 ^ 32 + y5.toNat = 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30 := by
    omega_using [v4, v5, la1, hR, hs]
  have eC : h0.toNat * 2 ^ 32 + c6.toNat = 4 * sv + 1 := by omega_using [v0, v6, hs]
  obtain ⟨sg, df⟩ := sub64_sign y4 y5 h0 c6 (by omega) (by omega)
  rw [eY, eC] at sg df
  rw [sg]
  have sb : (if 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30 < 4 * sv + 1 then 1 else 0) < 2 := by split <;> omega
  rw [sel_bit _ _ _ sb, sel_bit _ _ _ sb]
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_ofNat, g1, g2]; omega
  · rw [BitVec.toNat_shiftLeft, g2, Nat.shiftLeft_eq]
  · by_cases hc : 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30 < 4 * sv + 1
    · simp only [hc, ↓reduceIte, show ¬ (4 * sv + 1 ≤ 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30) by omega]
      rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, g3, e1, BitVec.toNat_ofNat]; omega
    · simp only [hc, ↓reduceIte, show 4 * sv + 1 ≤ 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30 by omega]
      rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, g3, e1, BitVec.toNat_ofNat]; omega
  · by_cases hc : 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30 < 4 * sv + 1
    · simp only [hc, ↓reduceIte, show ¬ (4 * sv + 1 ≤ 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30) by omega]
      rw [eY]; omega
    · simp only [hc, ↓reduceIte, show 4 * sv + 1 ≤ 4 * (rh * 2 ^ 32 + rl) + a1 / 2 ^ 30 by omega,
        show ¬ ((0 : Nat) = 1) by decide]
      exact df hc
  · rw [elr, (VG.Proof.Rsa.Arm.RecoverDet.cnt_sub hn llr).1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [elr, (cnt_sub hn llr).1, (cnt_sub hn llr).2]

section
variable {P : RP}

/-- `X := 1` where `X = 0` (`sZ`). -/
theorem bumpZ_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hR : wR ∈ LW) (hS : sZ ∈ LS) (hL : ∀ j ∈ L, j / 2 ≠ wR)
    (vZ : ∀ σ, E σ → V σ sZ = if AW σ wR = 0 then 1 else 0)
    (cert : DCert (.block (([.ldr .r2 .r8 sZ] : List Instr) ++ ptr .r0 wR ++
      ([.ldr .r1 .r0 0, .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r0 0] : List Instr)))) :
    VP (Dk P E A L AW LW V LS P.W 22)
      (.block (([.ldr .r2 .r8 sZ] : List Instr) ++ ptr .r0 wR ++ ([.ldr .r1 .r0 0, .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r0 0] : List Instr)))
      (Dk P E A L (fun σ => upd (AW σ) wR (if AW σ wR = 0 then 1 else AW σ wR)) LW V LS P.W 22) := by
  refine VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  have sz := h.sizes
  have Wl := sz.Wle
  have fR := fitZ_W sz (show wR < 22 by decide)
  simp only [S] at fR
  have Wp : 0 < P.W := by simp only [RP.W]; omega
  simp only [List.cons_append, List.nil_append]
  refine h.ldrSlot hv hS (r := .r2) (by decide) fun s1 h1 hv1 u1 => ?_
  refine ptr_ok hv1 (r := .r0) (by decide) (j := wR) (by decide) fun s2 p2 r2 m2 hv2 => ?_
  have h2 := h1.of_rest r2 m2 (by decide)
  refine wp_ldr (by decide) (arr_addr0 hv2 (show wR < 22 by decide) p2) (hv2.read (by omega)) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  have hv4 : Ws s4 P.B P.Z P.W 22 := (hv2.of_upd u3 (by decide) (by decide) (by decide)).of_upd u4 (by decide)
    (by decide) (by decide)
  refine storeLow_ok hv4 (j := wR) (by decide) (by rw [u4.other _ (by decide), u3.other _ (by decide), p2])
    fun t ht kt vt rt _ => WP.block_nil ⟨e, ?_, ht⟩
  have x0 := h.arrsW wR hR
  have rd : (s3.gpr .r1).toNat = AW σ wR % 2 ^ 32 := by
    rw [u3.gpr, m2, u1.mem, ← x0, num_mod32 _ _ Wp]
  have r2v : s3.gpr .r2 = BitVec.ofNat 32 (V σ sZ) := by
    rw [u3.other _ (by decide), r2.gpr _ (by decide), u1.gpr]
  have ev : num t.mem P.B P.W wR = if AW σ wR = 0 then 1 else AW σ wR := by
    rw [vt, u4.gpr, dpVal, r2v, vZ σ e, u4.mem, u3.mem, m2, u1.mem, x0]
    by_cases c : AW σ wR = 0
    · simp only [c, ↓reduceIte]
      have r0 : s3.gpr .r1 = 0#32 := BitVec.eq_of_toNat_eq (by rw [rd, c]; rfl)
      rw [r0]; rfl
    · simp only [c, ↓reduceIte]
      rw [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.or_zero, rd]; omega
  have k' : Keep P.B P.W [wR] [] s.mem t.mem := by rw [u4.mem, u3.mem, m2, u1.mem] at kt; exact kt
  have r' : Rest opRegs s t := ((u1.rest (by simp)).trans ((r2.mono (by simp)).trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans (rt.mono (by simp))))))
  exact (h.write_W k' (by decide) (by simp) (h.r8_of r') r'.sp r'.rd r'.wr ev hL (by simp)).mono
    (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)

end

section
variable {P : RP}
/-! ## The normalization -/

theorem lzc_spec {x N : Nat} (hx : x < 2 ^ N) : ∀ p, p ≤ N → x / 2 ^ (N - p) ≠ 0 →
    lzc x N p < p ∧ x / 2 ^ (N - lzc x N p - 1) ≠ 0 ∧ x / 2 ^ (N - lzc x N p) = 0
  | 0, _, h => by rw [Nat.sub_zero, Nat.div_eq_of_lt hx] at h; exact absurd rfl h
  | p + 1, hp, h => by
    have e : lzc x N (p + 1) = lzc x N p := by simp only [lzc, h, ↓reduceIte]
    rw [e]
    by_cases c : x / 2 ^ (N - p) = 0
    · rw [lzc_zero c]
      exact ⟨by omega, by rwa [show N - p - 1 = N - (p + 1) by omega], c⟩
    · have := lzc_spec hx p (by omega) c
      exact ⟨by omega, this.2⟩

/-- `X := 1` where it is 0, its leading zeros within `W` words, and it normalized. -/
abbrev xz (x : Nat) : Nat := if x = 0 then 1 else x
abbrev lzX (P : RP) (x : Nat) : Nat := lzc (xz x) (32 * P.W) (32 * P.W)
abbrev nX (P : RP) (x : Nat) : Nat := xz x * 4 ^ (lzX P x / 2)

theorem lz_bounds {x N : Nat} (h1 : 1 ≤ x) (hx : x < 2 ^ N) :
    lzc x N N < N ∧ 2 ^ (N - lzc x N N - 1) ≤ x ∧ x < 2 ^ (N - lzc x N N) := by
  have := lzc_spec hx N (Nat.le_refl _) (by rw [Nat.sub_self, Nat.pow_zero, Nat.div_one]; omega)
  obtain ⟨a, b, c⟩ := this
  refine ⟨a, ?_, ?_⟩
  · exact Nat.le_of_not_lt fun l => b (Nat.div_eq_of_lt l)
  · exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp c

/-- The normalized `X`: below `2^(32 W)`, at least `2^(32 W - 2)`. -/
theorem nX_bounds {x : Nat} (hx : x < 2 ^ (32 * P.W)) :
    2 ^ (32 * P.W - 2) ≤ nX P x ∧ nX P x < 2 ^ (32 * P.W) ∧ lzX P x < 32 * P.W := by
  have h1 : 1 ≤ xz x := by simp only [xz]; split <;> omega
  have hx' : xz x < 2 ^ (32 * P.W) := by
    simp only [xz]; split
    · exact Nat.one_lt_two_pow (by simp only [RP.W]; omega)
    · exact hx
  obtain ⟨a, b, c⟩ := lz_bounds h1 hx'
  simp only [nX, lzX] at *
  generalize lzc (xz x) (32 * P.W) (32 * P.W) = l at *
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]
  refine ⟨?_, ?_, a⟩
  · calc 2 ^ (32 * P.W - 2) ≤ 2 ^ (32 * P.W - l - 1 + 2 * (l / 2)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2 ^ (32 * P.W - l - 1) * 2 ^ (2 * (l / 2)) := Nat.pow_add ..
      _ ≤ xz x * 2 ^ (2 * (l / 2)) := Nat.mul_le_mul_right _ b
  · calc xz x * 2 ^ (2 * (l / 2)) < 2 ^ (32 * P.W - l) * 2 ^ (2 * (l / 2)) :=
          Nat.mul_lt_mul_of_pos_right c (Nat.two_pow_pos _)
      _ = 2 ^ (32 * P.W - l + 2 * (l / 2)) := (Nat.pow_add ..).symm
      _ ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by omega)

end

section
variable {P : RP}

/-- The slots after the normalization: whether `X = 0`, and the leading zeros. -/
abbrev VN (V : Nat → Nat) (x lz : Nat) : Nat → Nat := upd (upd V sZ (if x = 0 then 1 else 0)) sLz lz

/-- Drop a stage's scratch slots. -/
theorem drop_scratch {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat} {b : State → Nat}
    {v N : Nat} (hLS : ∀ d ∈ LS, d ≠ sBit ∧ d ≠ sK) {σ s : State}
    (h : Dk P E A L AW LW (fun σ => upd (upd (V σ) sBit (b σ)) sK 0) (sK :: sBit :: LS) v N σ s) :
    Dk P E A L AW LW V LS v N σ s :=
  ⟨h.1, h.2.1.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ hd), by simp only [upd_ne _ _ (hLS d hd).1, upd_ne _ _ (hLS d hd).2]⟩), h.2.2⟩

/-- The block between the bit stages and the word stages: `sTk := lz / 32`, `sWs := 4`. -/
theorem normMid_ok {lz : Nat} {σ s : State} {A AW V : Nat → Nat} {L LW LS : List Nat}
    (hS : sLz ∈ LS) (vS : V sLz = lz) (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.W 22) :
    WP isa (.block [.ldr .r1 .r8 sLz, .mov .r1 (.shifted .r1 .lsr 5), .str .r1 .r8 sTk,
      .mov .r1 (.imm 4), .str .r1 .r8 sWs]) s fun t =>
      KS P σ A L AW LW (WSV V (lz / 32) 0) (LSS LS) t ∧ Ws t P.B P.Z P.W 22 := by
  have b1 : lz < 2 ^ 32 := by rw [← vS, ← h.sl sLz hS]; exact BitVec.isLt _
  refine h.ldrSlot hv (d := sLz) hS (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2.strSlot hv2 (d := sTk) (r := .r1) (by decide) fun s3 h3 hv3 _ _ => ?_
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r1]) (by simp)) u4.mem
  refine h4.strSlot hv4 (d := sWs) (r := .r1) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨?_, hvt⟩
  have e2 : (s2.gpr .r1).toNat = lz / 32 := by
    rw [u2.gpr, u1.gpr, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, vS, Nat.mod_eq_of_lt b1,
      Nat.shiftRight_eq_div_pow]
  rw [e2, u4.gpr] at ht
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, ?_⟩)
  simp only [WSV, Nat.pow_zero, Nat.div_one, Nat.mul_one]; rfl

/-- `normX`: `X := 1` where `X = 0`, then `X' = 4^⌊lz / 2⌋ X`. -/
theorem normX_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hR : wR ∈ LW) (hZ : wZ ∈ LW) (z0 : ∀ σ, E σ → AW σ wZ = 0)
    (hLWT : ∀ j ∈ LW, j ≠ wG ∧ j ≠ wF ∧ j ≠ 18)
    (hL : ∀ j ∈ L, j / 2 ≠ wG ∧ j / 2 ≠ wF ∧ j / 2 ≠ wR ∧ j / 2 ≠ 18)
    (hLS : ∀ d ∈ LS, d ≠ sZ ∧ d ≠ sLz ∧ d ≠ sBit ∧ d ≠ sK ∧ d ≠ sTk ∧ d ≠ sWs ∧ (d + 4 ≤ sT ∨ sT + 4 ≤ d)) :
    VP (Dk P E A L AW LW V LS P.W 22) normX
      (Dk P E A L (fun σ => upd (AW σ) wR (nX P (AW σ wR))) LW
        (fun σ => VN (V σ) (AW σ wR) (lzX P (AW σ wR))) (sLz :: sZ :: LS) P.W 22) := by
  let E' := fun σ => E σ ∧ AW σ wR < 2 ^ (32 * P.W)
  refine VP.mono (F := Dk P E' A L AW LW V LS P.W 22) (G := Dk P E' A L (fun σ => upd (AW σ) wR (nX P (AW σ wR))) LW
      (fun σ => VN (V σ) (AW σ wR) (lzX P (AW σ wR))) (sLz :: sZ :: LS) P.W 22) ?_
    (fun σ s ⟨e, h, hv⟩ => ⟨⟨e, h.lt_W hR⟩, h, hv⟩) fun σ s ⟨e, h, hv⟩ => ⟨e.1, h, hv⟩
  have hRZ : wR ≠ wZ := by decide
  have lsN : ∀ d ∈ sLz :: sZ :: LS, d ≠ sBit ∧ d ≠ sK := fun d hd => by
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · decide
    · decide
    · exact ⟨(hLS d hd).2.2.1, (hLS d hd).2.2.2.1⟩
  have x1 : ∀ σ, E' σ → xz (AW σ wR) < 2 ^ (32 * P.W) := fun σ e => by
    simp only [xz]; split
    · exact Nat.one_lt_two_pow (by simp only [RP.W]; omega)
    · exact e.2
  simp only [normX, seqs]
  -- whether `X = 0`
  refine VP.seq (G := Dk P E' A L AW LW (fun σ => upd (V σ) sZ (if AW σ wR = 0 then 1 else 0)) (sZ :: LS) P.W 22)
    ((eqSW_vp (d := sZ) (a := wR) (b := wZ) (t := 18) hR hZ (by decide) (by decide)
      (fun h => (hLWT 18 h).2.2 rfl) (fun j hj => (hL j hj).2.2.2) (fun e he => (hLS e he).2.2.2.2.2.2) (by decide)
      eqSZ_taint).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩)
        (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, by simp only [z0 σ e.1]⟩), hv⟩) ?_
  -- `X := 1` there
  refine VP.seq (bumpZ_vp (P := P) hR (List.mem_cons_self ..) (fun j hj => (hL j hj).2.2.1)
    (fun σ _ => by rw [upd_self]) bumpZ_taint) ?_
  -- the leading zeros
  refine VP.seq (G := Dk P E' A L (fun σ => upd (AW σ) wR (xz (AW σ wR) * 2 ^ (2 * (lzX P (AW σ wR) / 2) % 2 ^ 1) %
      2 ^ (32 * P.W))) LW (fun σ => VN (V σ) (AW σ wR) (lzX P (AW σ wR))) (sLz :: sZ :: LS) P.W 22)
    ((lzW_vp (j := wR) (d := sLz) hR (by decide) lzW_taint).mono (fun _ _ h => h)
      fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩)
        (fun d hd => ⟨hd, ?_⟩), hv⟩) ?_
  · rfl
  · by_cases c : j = wR
    · subst c
      simp only [upd_self, show 2 * (lzX P (AW σ wR) / 2) % 2 ^ 1 = 0 by omega, Nat.pow_zero, Nat.mul_one,
        Nat.mod_eq_of_lt (x1 σ e)]
    · simp only [upd_ne _ _ c]
  · simp only [VN, upd_self, lzX, xz]
  -- the bit stages
  have st : ∀ i, 1 ≤ i → i < 5 → VP (Dk P E' A L
      (fun σ => upd (AW σ) wR (xz (AW σ wR) * 2 ^ (2 * (lzX P (AW σ wR) / 2) % 2 ^ i) % 2 ^ (32 * P.W))) LW
      (fun σ => VN (V σ) (AW σ wR) (lzX P (AW σ wR))) (sLz :: sZ :: LS) P.W 22) (normBitStage i)
      (Dk P E' A L (fun σ => upd (AW σ) wR (xz (AW σ wR) * 2 ^ (2 * (lzX P (AW σ wR) / 2) % 2 ^ (i + 1)) %
        2 ^ (32 * P.W))) LW (fun σ => VN (V σ) (AW σ wR) (lzX P (AW σ wR))) (sLz :: sZ :: LS) P.W 22) :=
    fun i h1 h5 => (normBitStage_vp (X := fun σ => xz (AW σ wR)) (t := fun σ => lzX P (AW σ wR)) h1 h5 hR
      (fun j hj => ⟨(hLWT j hj).1, (hLWT j hj).2.1⟩) (fun j hj => ⟨(hL j hj).1, (hL j hj).2.1, (hL j hj).2.2.1⟩)
      (List.mem_cons_self ..) (fun σ _ => by rw [upd_self]) (fun σ _ => by simp only [VN, upd_self])).mono
      (fun _ _ h => h) fun σ s h => ⟨h.1, (drop_scratch lsN h).2.1.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, by
        by_cases c : j = wR
        · subst c; simp only [upd_self]
        · simp only [upd_ne _ _ c]⟩) (fun d hd => ⟨hd, rfl⟩), h.2.2⟩
  refine (st 1 (by decide) (by decide)).seq ((st 2 (by decide) (by decide)).seq ((st 3 (by decide) (by decide)).seq
    ((st 4 (by decide) (by decide)).seq ?_)))
  -- the word stages
  let c := fun σ => 2 * (lzX P (AW σ wR) / 2) % 32
  let q := fun σ => lzX P (AW σ wR) / 32
  have lsS : ∀ d ∈ sLz :: sZ :: LS, d ≠ sBit ∧ d ≠ sTk ∧ d ≠ sWs := fun d hd => by
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · decide
    · decide
    · exact ⟨(hLS d hd).2.2.1, (hLS d hd).2.2.2.2.1, (hLS d hd).2.2.2.2.2.1⟩
  refine VP.seq (G := fun σ s => E' σ ∧ (KS P σ (A σ) L
      (upd (AW σ) wR (xz (AW σ wR) * 2 ^ (c σ + 32 * (q σ % 2 ^ 0)) % 2 ^ (32 * P.W))) LW
      (WSV (VN (V σ) (AW σ wR) (lzX P (AW σ wR))) (q σ) 0) (LSS (sLz :: sZ :: LS)) s ∧ Ws s P.B P.Z P.W 22))
    (VP.dctx normMid_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      WP.mono (normMid_ok (List.mem_cons_self ..) (by simp only [VN, upd_self]) h hv) fun t ⟨ht, hvt⟩ =>
        ⟨e, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, by
          by_cases cj : j = wR
          · subst cj
            simp only [upd_self, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.add_zero, c,
              show (2 : Nat) ^ (4 + 1) = 32 from rfl]
          · simp only [upd_ne _ _ cj]⟩) (fun d hd => ⟨hd, rfl⟩), hvt⟩) ?_
  refine (VP.count (E := E') (I := fun m σ s => KS P σ (A σ) L
      (upd (AW σ) wR (xz (AW σ wR) * 2 ^ (c σ + 32 * (q σ % 2 ^ m)) % 2 ^ (32 * P.W))) LW
      (WSV (VN (V σ) (AW σ wR) (lzX P (AW σ wR))) (q σ) m) (LSS (sLz :: sZ :: LS)) s ∧ Ws s P.B P.Z P.W 22)
    (by simp only [KWW]; omega) fun m hm =>
      normWordStage_vp (X := fun σ => xz (AW σ wR)) (c := c) (q := q) (V0 := fun σ => VN (V σ) (AW σ wR) (lzX P (AW σ wR)))
        hm hR hZ (fun σ e => z0 σ e.1) (fun j hj => ⟨(hLWT j hj).1, (hLWT j hj).2.1⟩)
        (fun j hj => ⟨(hL j hj).1, (hL j hj).2.1, (hL j hj).2.2.1⟩) lsS).mono (fun _ _ h => h)
    fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩)
      (fun d hd => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd), ?_⟩), hv⟩
  · by_cases cj : j = wR
    · subst cj
      simp only [upd_self]
      obtain ⟨-, nl, lzl⟩ := nX_bounds (P := P) e.2
      have qk : q σ < 2 ^ KWW P := Nat.lt_of_lt_of_le (by simp only [q]; omega) kww_ge
      rw [Nat.mod_eq_of_lt qk, show c σ + 32 * q σ = 2 * (lzX P (AW σ wR) / 2) by simp only [c, q]; omega]
      rw [show nX P (AW σ wR) = xz (AW σ wR) * 2 ^ (2 * (lzX P (AW σ wR) / 2)) by
        simp only [nX]; rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]] at nl ⊢
      exact Nat.mod_eq_of_lt nl
    · simp only [upd_ne _ _ cj]
  · simp only [WSV]
    rw [upd_ne _ _ (lsS d hd).2.2.symm.symm, upd_ne _ _ (lsS d hd).2.1]

end

/-! ## Stores of words -/

/-- `x` with its word `i` replaced by `v`. -/
abbrev setW (x i v : Nat) : Nat := x % 2 ^ (32 * i) + 2 ^ (32 * i) * (v + 2 ^ 32 * (x / 2 ^ (32 * (i + 1))))

/-- `x` with its `n` words from word `o` replaced by `v`. -/
abbrev setWin (x o n v : Nat) : Nat := x % 2 ^ (32 * o) + 2 ^ (32 * o) * (v + 2 ^ (32 * n) * (x / 2 ^ (32 * (o + n))))
/-- The complement over `W` words. -/
abbrev cmpl (W x : Nat) : Nat := 2 ^ (32 * W) - 1 - x

theorem pow32_add (a b : Nat) : (2 : Nat) ^ (32 * (a + b)) = 2 ^ (32 * a) * 2 ^ (32 * b) := by
  rw [Nat.mul_add, Nat.pow_add]

/-- Unique digits: `x = l + P q` with `l < P` gives `x % P = l` and `x / P = q`. -/
theorem mod_div_of {x l q P : Nat} (hP : 0 < P) (hl : l < P) (hx : x = l + P * q) : x % P = l ∧ x / P = q := by
  subst hx
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  · rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hl, Nat.zero_add]

theorem cmpl_split {W o x : Nat} (ho : o ≤ W) (hx : x < 2 ^ (32 * W)) :
    cmpl W x = (2 ^ (32 * o) - 1 - x % 2 ^ (32 * o)) + 2 ^ (32 * o) * (2 ^ (32 * (W - o)) - 1 - x / 2 ^ (32 * o)) := by
  have hW : 2 ^ (32 * W) = 2 ^ (32 * o) * 2 ^ (32 * (W - o)) := by rw [← pow32_add]; congr 2; omega
  have hm := Nat.mod_lt x (Nat.two_pow_pos (32 * o))
  have hd : x / 2 ^ (32 * o) < 2 ^ (32 * (W - o)) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← hW]; exact hx
  have e := Nat.mod_add_div x (2 ^ (32 * o))
  simp only [cmpl]
  generalize 2 ^ (32 * o) = P at *
  generalize 2 ^ (32 * (W - o)) = Q at *
  generalize x % P = l at *
  generalize x / P = q at *
  rw [hW, ← e]
  have h1 : P * q + P ≤ P * Q := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hd
  have h2 : P * (Q - 1 - q) = P * Q - P * q - P := by
    rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one]; omega
  rw [h2]
  have : P * q + P ≤ P * Q := h1
  have hl : l + 1 ≤ P := hm
  omega

theorem cmpl_mod_div {W o x : Nat} (ho : o ≤ W) (hx : x < 2 ^ (32 * W)) :
    cmpl W x % 2 ^ (32 * o) = 2 ^ (32 * o) - 1 - x % 2 ^ (32 * o) ∧
    cmpl W x / 2 ^ (32 * o) = 2 ^ (32 * (W - o)) - 1 - x / 2 ^ (32 * o) :=
  mod_div_of (Nat.two_pow_pos _) (by have := Nat.two_pow_pos (32 * o); omega) (cmpl_split ho hx)

theorem setWin_mod_div (x o n v : Nat) :
    setWin x o n v % 2 ^ (32 * o) = x % 2 ^ (32 * o) ∧
    setWin x o n v / 2 ^ (32 * o) = v + 2 ^ (32 * n) * (x / 2 ^ (32 * (o + n))) :=
  mod_div_of (Nat.two_pow_pos _) (Nat.mod_lt _ (Nat.two_pow_pos _)) rfl

theorem div_lt_of {x a b : Nat} (h : x < 2 ^ (32 * (a + b))) : x / 2 ^ (32 * a) < 2 ^ (32 * b) := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← pow32_add]; exact h

theorem setWin_lt {W x o n v : Nat} (hon : o + n ≤ W) (hx : x < 2 ^ (32 * W)) (hv : v < 2 ^ (32 * n)) :
    setWin x o n v < 2 ^ (32 * W) := by
  have hH : x / 2 ^ (32 * (o + n)) < 2 ^ (32 * (W - (o + n))) :=
    div_lt_of (by rw [show o + n + (W - (o + n)) = W by omega]; exact hx)
  have hW : 2 ^ (32 * W) = 2 ^ (32 * o) * (2 ^ (32 * n) * 2 ^ (32 * (W - (o + n)))) := by
    rw [← pow32_add, ← pow32_add]; congr 2; omega
  have hm := Nat.mod_lt x (Nat.two_pow_pos (32 * o))
  simp only [setWin]
  rw [hW]
  generalize 2 ^ (32 * o) = P at *
  generalize 2 ^ (32 * n) = Q at *
  generalize 2 ^ (32 * (W - (o + n))) = S at *
  generalize x / 2 ^ (32 * (o + n)) = H at *
  generalize x % P = l at *
  have h1 : v + Q * H + 1 ≤ Q * S := by
    have : Q * (H + 1) ≤ Q * S := Nat.mul_le_mul_left _ hH
    rw [Nat.mul_succ] at this; omega
  have h2 : P * (v + Q * H) + P ≤ P * (Q * S) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h1
  omega

theorem cmpl_setWin {W x o n v : Nat} (hon : o + n ≤ W) (hx : x < 2 ^ (32 * W)) (hv : v < 2 ^ (32 * n)) :
    cmpl W (setWin x o n v) = setWin (cmpl W x) o n (2 ^ (32 * n) - 1 - v) := by
  have hl := setWin_lt hon hx hv
  have c1 := cmpl_split (o := o) (by omega) hl
  obtain ⟨m1, d1⟩ := setWin_mod_div x o n v
  rw [m1, d1] at c1
  rw [c1]
  have c2 := cmpl_mod_div (o := o + n) (by omega) hx
  have c3 := cmpl_mod_div (o := o) (by omega) hx
  simp only [setWin]
  rw [c3.1, show (o + n) = o + n from rfl, c2.2]
  have hH : x / 2 ^ (32 * (o + n)) < 2 ^ (32 * (W - (o + n))) :=
    div_lt_of (by rw [show o + n + (W - (o + n)) = W by omega]; exact hx)
  have hR : 2 ^ (32 * (W - o)) = 2 ^ (32 * n) * 2 ^ (32 * (W - (o + n))) := by
    rw [← pow32_add]; congr 2; omega
  rw [hR]
  congr 1
  congr 1
  generalize 2 ^ (32 * n) = Q at *
  generalize 2 ^ (32 * (W - (o + n))) = S at *
  generalize x / 2 ^ (32 * (o + n)) = H at *
  have h1 : Q * H + Q ≤ Q * S := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hH
  have h2 : Q * (S - 1 - H) = Q * S - Q * H - Q := by rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one]; omega
  rw [h2]; omega

theorem win_cmpl {W x o n : Nat} (hon : o + n ≤ W) (hx : x < 2 ^ (32 * W)) :
    cmpl W x / 2 ^ (32 * o) % 2 ^ (32 * n) = 2 ^ (32 * n) - 1 - x / 2 ^ (32 * o) % 2 ^ (32 * n) := by
  rw [(cmpl_mod_div (o := o) (by omega) hx).2]
  have hd : x / 2 ^ (32 * o) < 2 ^ (32 * (W - o)) :=
    div_lt_of (by rw [show o + (W - o) = W by omega]; exact hx)
  have hR : 2 ^ (32 * (W - o)) = 2 ^ (32 * n) * 2 ^ (32 * (W - o - n)) := by
    rw [← pow32_add]; congr 2; omega
  rw [hR] at hd ⊢
  have e := Nat.mod_add_div (x / 2 ^ (32 * o)) (2 ^ (32 * n))
  have hm := Nat.mod_lt (x / 2 ^ (32 * o)) (Nat.two_pow_pos (32 * n))
  generalize x / 2 ^ (32 * o) = y at *
  generalize 2 ^ (32 * n) = Q at *
  generalize 2 ^ (32 * (W - o - n)) = S at *
  generalize y % Q = l at *
  generalize y / Q = q at *
  subst e
  have hq : q < S := by
    by_contra hc
    have : Q * S ≤ Q * q := Nat.mul_le_mul_left _ (by omega)
    omega
  have : Q * S - 1 - (l + Q * q) = (Q - 1 - l) + Q * (S - 1 - q) := by
    have h1 : Q * q + Q ≤ Q * S := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hq
    have h2 : Q * (S - 1 - q) = Q * S - Q * q - Q := by rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one]; omega
    rw [h2]; omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem setW_eq_win (x i v : Nat) : setW x i v = setWin x i 1 v := by
  simp only [setW, setWin, Nat.mul_one]

theorem cmpl_setW {W x i v : Nat} (hi : i < W) (hx : x < 2 ^ (32 * W)) (hv : v < 2 ^ 32) :
    cmpl W (setW x i v) = setW (cmpl W x) i (2 ^ 32 - 1 - v) := by
  rw [setW_eq_win, setW_eq_win, cmpl_setWin (by omega) hx hv]

theorem setW_lt {W x i v : Nat} (hi : i < W) (hx : x < 2 ^ (32 * W)) (hv : v < 2 ^ 32) :
    setW x i v < 2 ^ (32 * W) := by
  rw [setW_eq_win]; exact setWin_lt (by omega) hx hv

theorem setWin_adj {x o n k a b : Nat} (ha : a < 2 ^ (32 * n)) :
    setWin (setWin x o n a) (o + n) k b = setWin x o (n + k) (a + 2 ^ (32 * n) * b) := by
  have hm := Nat.mod_lt x (Nat.two_pow_pos (32 * o))
  have y1 : setWin x o n a % 2 ^ (32 * (o + n)) = x % 2 ^ (32 * o) + 2 ^ (32 * o) * a ∧
      setWin x o n a / 2 ^ (32 * (o + n)) = x / 2 ^ (32 * (o + n)) := by
    refine mod_div_of (Nat.two_pow_pos _) ?_ ?_
    · rw [pow32_add]
      have : 2 ^ (32 * o) * a + 2 ^ (32 * o) ≤ 2 ^ (32 * o) * 2 ^ (32 * n) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ha
      omega
    · simp only [setWin]; rw [pow32_add]; ring
  have e3 : ∀ y : Nat, y / 2 ^ (32 * (o + n + k)) = y / 2 ^ (32 * (o + n)) / 2 ^ (32 * k) := fun y => by
    rw [Nat.div_div_eq_div_mul, ← pow32_add]
  simp only [setWin] at y1 ⊢
  rw [y1.1, e3, y1.2, ← e3, show o + n + k = o + (n + k) by omega, pow32_add n k, pow32_add o n]
  ring


theorem val32_write_at (m : Mem) (base : Addr) {d i k : Nat} (v : BitVec 32) (hi : i < k)
    (fit : d + 4 * k ≤ 2 ^ 64) :
    val32 (m.writeW (off base (d + 4 * i)) v) base d k = setW (val32 m base d k) i v.toNat := by
  have o := writeW32_outside m base (d := d + 4 * i) v (by omega)
  obtain ⟨r, rfl⟩ : ∃ r, k = i + (r + 1) := ⟨k - i - 1, by omega⟩
  have sp : ∀ m' : Mem, val32 m' base d (i + (r + 1)) =
      val32 m' base d i + 2 ^ (32 * i) * (w32 m' base (d + 4 * i) + 2 ^ 32 * val32 m' base (d + 4 * i + 4) r) :=
    fun m' => by rw [val32_append]; rfl
  have e1 : val32 (m.writeW (off base (d + 4 * i)) v) base d i = val32 m base d i := o.val32 (by omega) (by omega)
  have e2 : w32 (m.writeW (off base (d + 4 * i)) v) base (d + 4 * i) = v.toNat := w32_write_self ..
  have e3 : val32 (m.writeW (off base (d + 4 * i)) v) base (d + 4 * i + 4) r = val32 m base (d + 4 * i + 4) r :=
    o.val32 (by omega) (by omega)
  have lo := val32_lt m base d i
  have wl := (m.readW (off base (d + 4 * i)) 32).isLt
  have hi' := val32_lt m base (d + 4 * i + 4) r
  rw [sp, sp, e1, e2, e3]
  simp only [setW]
  have pi := Nat.two_pow_pos (32 * i)
  have q1 : (val32 m base d i + 2 ^ (32 * i) * (w32 m base (d + 4 * i) + 2 ^ 32 * val32 m base (d + 4 * i + 4) r)) %
      2 ^ (32 * i) = val32 m base d i := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lo]
  have q2 : (val32 m base d i + 2 ^ (32 * i) * (w32 m base (d + 4 * i) + 2 ^ 32 * val32 m base (d + 4 * i + 4) r)) /
      2 ^ (32 * (i + 1)) = val32 m base (d + 4 * i + 4) r := by
    rw [show 32 * (i + 1) = 32 * i + 32 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ pi, Nat.div_eq_of_lt lo, Nat.zero_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (show w32 m base (d + 4 * i) < 2 ^ 32 from wl), Nat.zero_add]
  rw [q1, q2]

section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

theorem wp_mvn {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {o : Op2} {v : BitVec 32}
    (ho : o.eval s = some v) (k : ∀ s', Upd s s' d (~~~v) → WP isa (.block is) s' Q) :
    WP isa (.block (.mvn d o :: is)) s Q :=
  WP.cons (s' := s.setReg d (~~~v)) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

/-- `str r, [rb, #o]` with `rb` at word `i0` of the wide `[j]`: its word `i = i0 + o / 4` := `r`. -/
theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.strWo {j i i0 o : Nat} {r rb : Reg} (h : KS P σ A live AW liveW V ls s)
    (hv : VG.Proof.Rsa.Arm.KeyDiv.WsM s P.B P.Z P.W 22) (hj : j ∈ liveW) (hi : i < P.W) (ho : 4 * i0 + o = 4 * i) (hoff : o < 4096)
    (p : s.gpr rb = P.B + BitVec.ofNat 32 (arr P.W j + 4 * i0))
    (hl : ∀ i ∈ live, i / 2 ≠ j) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live (upd AW j (setW (AW j) i (s.gpr r).toNat)) (j :: liveW) V ls t →
      VG.Proof.Rsa.Arm.KeyDiv.WsM t P.B P.Z P.W 22 → t.gpr = s.gpr → t.wr = s.wr → WP isa (.block rest) t Q) :
    WP isa (.block (.str r rb o :: rest)) s Q := by
  have sz := h.sizes
  have Wl := sz.Wle
  have j22 := h.liveW_lt j hj
  have fj := fitZ_W sz j22
  have fj' := fit_W sz j22
  have nw := hv.nowrap
  simp only [S] at fj fj'
  have ad : State.addr (s.gpr rb + BitVec.ofNat 32 o) = off (State.addr P.B) (arr P.W j + 4 * i) := by
    rw [p, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc, show arr P.W j + 4 * i0 + o = arr P.W j + 4 * i by omega,
      hv.addr (by omega)]
  refine wp_str hoff ad (hv.write (by omega)) fun t u => ?_
  have O := writeW32_outside s.mem (State.addr P.B) (d := arr P.W j + 4 * i) (s.gpr r) (by omega)
  have kt : Keep P.B P.W [j] [] s.mem t.mem := by
    rw [u.mem]; exact Keep.of_arr (d := 4 * i) O (by simp only [S]; omega) (by simp)
  have ev : num t.mem P.B P.W j = setW (AW j) i (s.gpr r).toNat := by
    rw [u.mem, ← h.arrsW j hj]
    exact val32_write_at _ _ _ hi (by omega)
  exact k t (h.write_W kt j22 (by simp) (by rw [u.gpr, h.r8]) u.sp u.rd u.wr ev hl (by simp)) (hv.of u.wr) u.gpr u.wr

/-- `ldr r, [rb, #o]` with `rb` at word `i0` of the wide `[j]`: `r :=` its word `i = i0 + o / 4`. -/
theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.ldrWo {j i i0 o : Nat} {r rb : Reg} (h : KS P σ A live AW liveW V ls s)
    (hv : VG.Proof.Rsa.Arm.KeyDiv.WsM s P.B P.Z P.W 22) (hj : j ∈ liveW) (hi : i < P.W) (ho : 4 * i0 + o = 4 * i) (hoff : o < 4096)
    (p : s.gpr rb = P.B + BitVec.ofNat 32 (arr P.W j + 4 * i0)) (hr : r ∉ [.r7, .r8, .r9])
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW V ls t → VG.Proof.Rsa.Arm.KeyDiv.WsM t P.B P.Z P.W 22 →
      Upd s t r (BitVec.ofNat 32 (AW j / 2 ^ (32 * i) % 2 ^ 32)) → WP isa (.block rest) t Q) :
    WP isa (.block (.ldr r rb o :: rest)) s Q := by
  have sz := h.sizes
  have Wl := sz.Wle
  have j22 := h.liveW_lt j hj
  have fj := fitZ_W sz j22
  have fj' := fit_W sz j22
  have nw := hv.nowrap
  simp only [S] at fj fj'
  have ad : State.addr (s.gpr rb + BitVec.ofNat 32 o) = off (State.addr P.B) (arr P.W j + 4 * i) := by
    rw [p, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc, show arr P.W j + 4 * i0 + o = arr P.W j + 4 * i by omega,
      hv.addr (by omega)]
  refine wp_ldr hoff ad (hv.read (by omega)) fun t u => ?_
  have e : s.mem.readW (off (State.addr P.B) (arr P.W j + 4 * i)) 32 =
      BitVec.ofNat 32 (AW j / 2 ^ (32 * i) % 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    have w := w32_digit s.mem (State.addr P.B) (arr P.W j) hi (n := P.W)
    have x0 := h.arrsW j hj
    simp only [num] at x0
    rw [x0] at w
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
    exact w
  rw [e] at u
  have h7 : r ≠ .r7 := fun e => hr (by simp [e])
  have h8 : r ≠ .r8 := fun e => hr (by simp [e])
  have h9 : r ≠ .r9 := fun e => hr (by simp [e])
  exact k t (h.of_rest (u.rest (ws := [r]) (by simp)) u.mem (by simpa using h8.symm)) (hv.of u.wr) u

end

/-! ## The first digit's math -/

open VG.Proof.Bignum.SqrtRem (sqrt_of_rem) in
/-- A pair of bits `d` brought into the root `s` and remainder `r` of `A`. -/
theorem isq_step {s r A d : Nat} (h : s * s + r = A) (hr : r ≤ 2 * s) (hd : d < 4) :
    let q := if 4 * s + 1 ≤ 4 * r + d then 1 else 0
    (2 * s + q) * (2 * s + q) + (4 * r + d - (if 4 * s + 1 ≤ 4 * r + d then 4 * s + 1 else 0)) = 4 * A + d ∧
      4 * r + d - (if 4 * s + 1 ≤ 4 * r + d then 4 * s + 1 else 0) ≤ 2 * (2 * s + q) := by
  intro q
  have e0 : (2 * s + 0) * (2 * s + 0) = 4 * (s * s) := by ring
  have e1 : (2 * s + 1) * (2 * s + 1) = 4 * (s * s) + 4 * s + 1 := by ring
  by_cases c : 4 * s + 1 ≤ 4 * r + d
  · simp only [q, c, ↓reduceIte, e1]; omega
  · simp only [q, c, ↓reduceIte, e0]; omega

theorem four_pow_eq (k : Nat) : (4 : Nat) ^ k = 2 ^ (2 * k) := by
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]

/-- The top pair of bits of `T 4^k` (64 bits) is the next pair of `T` below its top `2 k` bits. -/
theorem isq_shift {T k : Nat} (hk : k < 32) :
    T / 4 ^ (31 - k) = 4 * (T / 4 ^ (32 - k)) + T * 4 ^ k % 2 ^ 64 / 2 ^ 62 ∧
      T * 4 ^ (k + 1) % 2 ^ 64 = T * 4 ^ k % 2 ^ 64 * 4 % 2 ^ 64 := by
  have m4 : ∀ a b : Nat, 4 ^ a * 4 ^ b = 4 ^ (a + b) := fun a b => (Nat.pow_add ..).symm
  have e64 : (2 : Nat) ^ 64 = 4 ^ (32 - k) * 4 ^ k := by rw [m4, four_pow_eq]; congr 1; omega
  have e62 : (2 : Nat) ^ 62 = 4 ^ (31 - k) * 4 ^ k := by rw [m4, four_pow_eq]; congr 1; omega
  have e32 : (4 : Nat) ^ (32 - k) = 4 ^ (31 - k) * 4 := by rw [← Nat.pow_succ]; congr 1; omega
  refine ⟨?_, ?_⟩
  · rw [e64, e62, Nat.mul_mod_mul_right, Nat.mul_div_mul_right _ _ (Nat.pow_pos (by decide)), e32,
      Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (T / 4 ^ (31 - k)) 4
    omega
  · rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod, Nat.mod_eq_of_lt (show (4 : Nat) < 2 ^ 64 by decide)]

section
variable {P : RP}
open VG.Proof.Rsa.RecoverDet (isqrt_sq_le lt_succ_isqrt_sq)
open VG.Spec.Rsa (isqrt)

/-- After `k` pairs of the top 64 bits `T`: the bits left in `r1`, `r2`, the root of the pairs taken in
`r3` and their remainder in `r4`, `r5`, `32 - k` in `lr`. -/
abbrev IQ (T k : Nat) (s : State) : Prop :=
  (s.gpr .r1).toNat = T * 4 ^ k % 2 ^ 64 / 2 ^ 32 ∧ (s.gpr .r2).toNat = T * 4 ^ k % 2 ^ 64 % 2 ^ 32 ∧
    (s.gpr .r3).toNat = isqrt (T / 4 ^ (32 - k)) ∧
    (s.gpr .r4).toNat * 2 ^ 32 + (s.gpr .r5).toNat =
      T / 4 ^ (32 - k) - isqrt (T / 4 ^ (32 - k)) * isqrt (T / 4 ^ (32 - k)) ∧
    (s.gpr .lr).toNat = 32 - k

theorem isq_root_lt {T k : Nat} (hT : T < 2 ^ 64) (hk : k ≤ 32) : isqrt (T / 4 ^ (32 - k)) < 2 ^ k := by
  have hA : T / 4 ^ (32 - k) < 4 ^ k := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_add, four_pow_eq, show 2 * (k + (32 - k)) = 64 by
      omega]; exact hT
  refine Nat.lt_of_not_le fun c => ?_
  have := Nat.mul_le_mul c c
  rw [← Nat.pow_add, show k + k = 2 * k by omega, ← four_pow_eq] at this
  have := isqrt_sq_le (T / 4 ^ (32 - k))
  omega

theorem isqLoop_ok {T : Nat} (hT : T < 2 ^ 64) {σ s : State} {A AW V : Nat → Nat} {L LW LS : List Nat}
    (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.W 22) (c : IQ T 0 s) :
    WP isa (.loop (.block isqBit) .ne) s fun t => KS P σ A L AW LW V LS t ∧ Ws t P.B P.Z P.W 22 ∧ IQ T 32 t := by
  refine wp_count (K := 32) (I := fun k t => KS P σ A L AW LW V LS t ∧ Ws t P.B P.Z P.W 22 ∧ IQ T k t) (by decide)
    (fun k hk t ⟨ht, hvt, q1, q2, q3, q45, ql⟩ => ?_) ⟨h, hv, c⟩
  obtain ⟨sh, nx⟩ := isq_shift (T := T) hk
  generalize eA : T / 4 ^ (32 - k) = Ak at *
  generalize eU : T * 4 ^ k % 2 ^ 64 = U at *
  have hU : U < 2 ^ 64 := by rw [← eU]; exact Nat.mod_lt _ (by decide)
  have sl := isq_root_lt hT (show k ≤ 32 by omega)
  rw [eA] at sl
  have lo := isqrt_sq_le Ak
  have hi := lt_succ_isqrt_sq Ak
  have e2 : (isqrt Ak + 1) * (isqrt Ak + 1) = isqrt Ak * isqrt Ak + 2 * isqrt Ak + 1 := by ring
  refine WP.mono (isqBit_ok q1 q2 q3 rfl rfl ql (Nat.lt_of_lt_of_le sl (Nat.pow_le_pow_right (by decide) (by omega)))
    (by omega) (by omega)) fun t' ⟨⟨t1, t2, t3, t45, tl, tz, tm⟩, R⟩ => ?_
  obtain ⟨ht', hvt'⟩ := ht.reg hvt R tm
  have hd : U / 2 ^ 32 / 2 ^ 30 = U / 2 ^ 62 := by omega
  rw [q45, hd] at t3 t45
  obtain ⟨st1, st2⟩ := isq_step (s := isqrt Ak) (r := Ak - isqrt Ak * isqrt Ak) (A := Ak) (d := U / 2 ^ 62)
    (by omega) (by omega) (by omega)
  have sq := VG.Proof.Bignum.SqrtRem.sqrt_of_rem st1 st2
  refine ⟨⟨ht', hvt', ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [t1, nx]; omega
  · rw [t2, nx]; omega
  · rw [t3, show 32 - (k + 1) = 31 - k by omega, sh, sq]
  · rw [t45, show 32 - (k + 1) = 31 - k by omega, sh, sq]; omega
  · rw [tl]; omega
  · rw [tz, show 32 - k - 1 = 32 - (k + 1) by omega]

end

section
variable {P : RP}
open VG.Spec.Rsa (isqrt)

/-- The top 64 bits of the normalized `X`. -/
abbrev topT (P : RP) (x : Nat) : Nat := x / 2 ^ (32 * (P.W - 2))

theorem isqrt_zero : isqrt 0 = 0 := by unfold isqrt; rfl

theorem topT_lt {x : Nat} (hx : x < 2 ^ (32 * P.W)) (hW : 2 ≤ P.W) : topT P x < 2 ^ 64 := by
  simp only [topT]
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 64 + 32 * (P.W - 2) = 32 * P.W by omega]
  exact hx

/-- `isqTop`: the root `s₀` of the top 64 bits `T` into the slot `sD`, `T - s₀²` in place of `X'`'s top two
words, `D = 2 s₀` into the zero `[wD]`'s words `W / 2 - 1` and `W / 2`, and its complement into `[wE]`. -/
theorem isqTop_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hR : wR ∈ LW) (hD : wD ∈ LW) (hE : wE ∈ LW) (d0 : ∀ σ, E σ → AW σ wD = 0)
    (c0 : ∀ σ, E σ → AW σ wE = cmpl P.W 0) (hL : ∀ j ∈ L, j / 2 ≠ wR ∧ j / 2 ≠ wD ∧ j / 2 ≠ wE) :
    VP (Dk P E A L AW LW V LS P.W 22) isqTop
      (Dk P E A L (fun σ => upd (upd (upd (AW σ) wR
          (setWin (AW σ wR) (P.W - 2) 2 (topT P (AW σ wR) - isqrt (topT P (AW σ wR)) * isqrt (topT P (AW σ wR)))))
          wD (setWin 0 (P.W / 2 - 1) 2 (2 * isqrt (topT P (AW σ wR)))))
          wE (cmpl P.W (setWin 0 (P.W / 2 - 1) 2 (2 * isqrt (topT P (AW σ wR)))))) LW
        (fun σ => upd (V σ) VG.Impl.Rsa.Arm.KeyDiv.sD (isqrt (topT P (AW σ wR))))
        (VG.Impl.Rsa.Arm.KeyDiv.sD :: LS) P.W 22) := by
  refine VP.dctx isqTop_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  have sz := h.sizes
  have Wl := sz.Wle
  have W4 : 4 ≤ P.W := by simp only [RP.W, RP.w]; omega
  have fR := fitZ_W sz (show wR < 22 by decide)
  have nw := hv.nowrap
  simp only [S] at fR
  have xl := h.lt_W hR
  have Tl := topT_lt xl (by omega)
  generalize eT : topT P (AW σ wR) = T at Tl ⊢
  have x0 := h.arrsW wR hR
  simp only [isqTop, seqs]
  refine WP.seq ?_
  refine ptr_ok hv (r := .r0) (by decide) (j := wR) (by decide) fun s1 p1 r1 m1 hv1 => ?_
  have h1 := h.of_rest r1 m1 (by decide)
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r0]) (by simp)) u3.mem
  have p3 : s3.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W wR + 4 * (P.W - 2)) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, hv1.r7, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, sub_ofNat_eq _ (by simp only [S]; omega) (by decide)]
    congr 2
  have w0 : w32 s3.mem (State.addr P.B) (arr P.W wR + 4 * (P.W - 2)) = T % 2 ^ 32 := by
    rw [u3.mem, u2.mem, m1]
    have := w32_digit s.mem (State.addr P.B) (arr P.W wR) (show P.W - 2 < P.W by omega)
    rw [this]; simp only [num] at x0; rw [x0, ← eT]
  have w1 : w32 s3.mem (State.addr P.B) (arr P.W wR + 4 * (P.W - 2) + 4) = T / 2 ^ 32 := by
    rw [u3.mem, u2.mem, m1, show arr P.W wR + 4 * (P.W - 2) + 4 = arr P.W wR + 4 * (P.W - 1) by omega]
    have := w32_digit s.mem (State.addr P.B) (arr P.W wR) (show P.W - 1 < P.W by omega)
    rw [this]; simp only [num] at x0; rw [x0, ← eT, topT, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 32 * (P.W - 2) + 32 = 32 * (P.W - 1) by omega]
    refine Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr ?_)
    rw [← Nat.pow_add, show 32 + 32 * (P.W - 1) = 32 * P.W by omega]; exact xl
  refine wp_ldr (by decide) (by rw [p3, BitVec.add_zero, hv3.addr (by omega)]) (hv3.read (by omega)) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r2]) (by simp)) u4.mem
  refine wp_ldr (by decide) (by rw [u4.other _ (by decide), p3, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc,
    hv4.addr (by omega)]) (hv4.read (by omega)) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r3]) (by simp)) u6.mem
  refine wp_mov (op2_imm (by decide)) fun s7 u7 => ?_
  obtain ⟨h7, hv7⟩ := h6.reg hv6 (u7.rest (ws := [.r4]) (by simp)) u7.mem
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  obtain ⟨h8, hv8⟩ := h7.reg hv7 (u8.rest (ws := [.r5]) (by simp)) u8.mem
  refine wp_mov (op2_imm (by decide)) fun s9 u9 => ?_
  obtain ⟨h9, hv9⟩ := h8.reg hv8 (u9.rest (ws := [.lr]) (by simp)) u9.mem
  refine WP.block_nil (WP.seq (WP.mono (isqLoop_ok Tl h9 hv9 ⟨?_, ?_, ?_, ?_, ?_⟩) fun t ⟨ht, hvt, q1, q2, q3, q45, ql⟩ => ?_))
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr,
      u4.mem]
    show w32 s3.mem (State.addr P.B) (arr P.W wR + 4 * (P.W - 2) + 4) = _
    rw [w1, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt Tl]
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.gpr]
    show w32 s3.mem (State.addr P.B) (arr P.W wR + 4 * (P.W - 2)) = _
    rw [w0, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt Tl]
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.gpr,
      Nat.div_eq_of_lt (show T < 4 ^ (32 - 0) by rw [four_pow_eq]; exact Tl), isqrt_zero]; rfl
  · have g4 : (s9.gpr .r4).toNat = 0 := by rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr]; rfl
    have g5 : (s9.gpr .r5).toNat = 0 := by rw [u9.other _ (by decide), u8.gpr]; rfl
    rw [g4, g5, Nat.div_eq_of_lt (show T < 4 ^ (32 - 0) by rw [four_pow_eq]; exact Tl), isqrt_zero]; rfl
  · rw [u9.gpr]; rfl
  rw [Nat.sub_self, Nat.pow_zero, Nat.div_one] at q3 q45
  have sl := isq_root_lt Tl (le_refl 32)
  rw [Nat.sub_self, Nat.pow_zero, Nat.div_one] at sl
  have hW2 : P.W = 2 * (P.W / 2) := by simp only [RP.W]; omega
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- the remainder into `X'`'s top two words
  refine ptr_ok hvt (r := .r0) (by decide) (j := wR) (by decide) fun t1 p1' r1' m1' hv1' => ?_
  have ht1 := ht.of_rest r1' m1' (by decide)
  refine wp_dp (op2_reg _ _) fun t2 u2' => ?_
  obtain ⟨ht2, hv2'⟩ := ht1.reg hv1' (u2'.rest (ws := [.r0]) (by simp)) u2'.mem
  refine wp_dp (op2_imm (by decide)) fun t3 u3' => ?_
  obtain ⟨ht3, hv3'⟩ := ht2.reg hv2' (u3'.rest (ws := [.r0]) (by simp)) u3'.mem
  have q0 : t3.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W wR + 4 * (P.W - 2)) := by
    rw [u3'.gpr, dpVal, u2'.gpr, dpVal, p1', hv1'.r7, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, sub_ofNat_eq _ (by simp only [S]; omega) (by decide)]
    congr 2
  have g3 : ∀ r, r ≠ .r0 → t3.gpr r = t.gpr r := fun r hr => by
    rw [u3'.other _ hr, u2'.other _ hr, r1'.gpr _ (by simpa using hr)]
  refine ht3.strWo hv3'.m hR (i := P.W - 2) (i0 := P.W - 2) (by omega) (by omega) (by decide) q0
    (fun j hj => (hL j hj).1) fun t4 ht4 hv4 e4 w4 => ?_
  refine ht4.strWo hv4 (List.mem_cons_self ..) (i := P.W - 1) (i0 := P.W - 2) (by omega) (by omega) (by decide)
    (by rw [e4, q0]) (fun j hj => (hL j hj).1) fun t5 ht5 hv5 e5 w5 => ?_
  have hv5' : Ws t5 P.B P.Z P.W 22 := hv3'.of (by rw [e5, e4]) (by rw [e5, e4]) (by rw [e5, e4]) (w5.trans w4)
  refine ht5.strSlot hv5' (d := VG.Impl.Rsa.Arm.KeyDiv.sD) (r := .r3) (by decide) fun t6 ht6 hv6 e6 _ => ?_
  -- `2 s₀` into `D`'s words `W / 2 - 1` and `W / 2`
  refine ptr_ok hv6 (r := .r0) (by decide) (j := wD) (by decide) fun t7 p7 r7' m7 hv7 => ?_
  have ht7 := ht6.of_rest r7' m7 (by decide)
  refine wp_dp (op2_lsl (by decide)) fun t8 u8' => ?_
  obtain ⟨ht8, hv8⟩ := ht7.reg hv7 (u8'.rest (ws := [.r0]) (by simp)) u8'.mem
  refine wp_dp (op2_imm (by decide)) fun t9 u9' => ?_
  obtain ⟨ht9, hv9⟩ := ht8.reg hv8 (u9'.rest (ws := [.r0]) (by simp)) u9'.mem
  have fD := fitZ_W sz (show wD < 22 by decide)
  have fE := fitZ_W sz (show wE < 22 by decide)
  simp only [S] at fD fE
  have q9 : t9.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W wD + 4 * (P.W / 2 - 1)) := by
    rw [u9'.gpr, dpVal, u8'.gpr, dpVal, p7, hv7.r9, VG.Proof.Rsa.Arm.KeyDiv.shl1_val (by omega),
      VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
      sub_ofNat_eq _ (by omega) (by decide)]
    congr 2; omega
  have r3_9 : t9.gpr .r3 = t.gpr .r3 := by
    rw [u9'.other _ (by decide), u8'.other _ (by decide), r7'.gpr _ (by decide), e6, e5, e4, g3 _ (by decide)]
  refine wp_dp (op2_reg _ _) fun t10 u10 => ?_
  obtain ⟨ht10, hv10⟩ := ht9.reg hv9 (u10.rest (ws := [.r1]) (by simp)) u10.mem
  refine wp_mov (op2_lsr (by decide)) fun t11 u11 => ?_
  obtain ⟨ht11, hv11⟩ := ht10.reg hv10 (u11.rest (ws := [.r2]) (by simp)) u11.mem
  have va : (t11.gpr .r1).toNat = 2 * isqrt T % 2 ^ 32 := by
    rw [u11.other _ (by decide), u10.gpr, dpVal, r3_9, BitVec.toNat_add, q3]
    congr 1; omega
  have vb : (t11.gpr .r2).toNat = isqrt T / 2 ^ 31 := by
    rw [u11.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, u10.other _ (by decide), r3_9, q3]
  refine ht11.strWo hv11.m (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hD)) (i := P.W / 2 - 1) (i0 := P.W / 2 - 1) (by omega)
    (by omega) (by decide) (by rw [u11.other _ (by decide), u10.other _ (by decide), q9])
    (fun j hj => (hL j hj).2.1) fun t12 ht12 hv12 e12 w12 => ?_
  refine ht12.strWo hv12 (List.mem_cons_self ..) (i := P.W / 2) (i0 := P.W / 2 - 1) (by omega) (by omega) (by decide)
    (by rw [e12, u11.other _ (by decide), u10.other _ (by decide), q9]) (fun j hj => (hL j hj).2.1)
    fun t13 ht13 hv13 e13 w13 => ?_
  have hv13' : Ws t13 P.B P.Z P.W 22 :=
    hv11.of (by rw [e13, e12]) (by rw [e13, e12]) (by rw [e13, e12]) (w13.trans w12)
  -- its complement into `C`'s
  refine ptr_ok hv13' (r := .r0) (by decide) (j := wE) (by decide) fun t14 p14 r14 m14 hv14 => ?_
  have ht14 := ht13.of_rest r14 m14 (by decide)
  refine wp_dp (op2_lsl (by decide)) fun t15 u15 => ?_
  obtain ⟨ht15, hv15⟩ := ht14.reg hv14 (u15.rest (ws := [.r0]) (by simp)) u15.mem
  refine wp_dp (op2_imm (by decide)) fun t16 u16 => ?_
  obtain ⟨ht16, hv16⟩ := ht15.reg hv15 (u16.rest (ws := [.r0]) (by simp)) u16.mem
  have q16 : t16.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W wE + 4 * (P.W / 2 - 1)) := by
    rw [u16.gpr, dpVal, u15.gpr, dpVal, p14, hv14.r9, VG.Proof.Rsa.Arm.KeyDiv.shl1_val (by omega),
      VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
      sub_ofNat_eq _ (by omega) (by decide)]
    congr 2; omega
  have r12_16 : ∀ r, r = .r1 ∨ r = .r2 → t16.gpr r = t11.gpr r := fun r hr => by
    rcases hr with rfl | rfl <;>
      rw [u16.other _ (by decide), u15.other _ (by decide), r14.gpr _ (by decide), e13, e12]
  refine wp_mvn (op2_reg _ _) fun t17 u17 => ?_
  obtain ⟨ht17, hv17⟩ := ht16.reg hv16 (u17.rest (ws := [.r1]) (by simp)) u17.mem
  refine wp_mvn (op2_reg _ _) fun t18 u18 => ?_
  obtain ⟨ht18, hv18⟩ := ht17.reg hv17 (u18.rest (ws := [.r2]) (by simp)) u18.mem
  have na : (t18.gpr .r1).toNat = 2 ^ 32 - 1 - 2 * isqrt T % 2 ^ 32 := by
    rw [u18.other _ (by decide), u17.gpr, BitVec.toNat_not, r12_16 _ (Or.inl rfl), va]
  have nb : (t18.gpr .r2).toNat = 2 ^ 32 - 1 - isqrt T / 2 ^ 31 := by
    rw [u18.gpr, BitVec.toNat_not, u17.other _ (by decide), r12_16 _ (Or.inr rfl), vb]
  have hE6 : wE ∈ wD :: wD :: wR :: wR :: LW :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hE)))
  refine ht18.strWo hv18.m hE6 (i := P.W / 2 - 1) (i0 := P.W / 2 - 1) (by omega) (by omega) (by decide)
    (by rw [u18.other _ (by decide), u17.other _ (by decide), q16]) (fun j hj => (hL j hj).2.2)
    fun t19 ht19 hv19 e19 w19 => ?_
  refine ht19.strWo hv19 (List.mem_cons_self ..) (i := P.W / 2) (i0 := P.W / 2 - 1) (by omega) (by omega) (by decide)
    (by rw [e19, u18.other _ (by decide), u17.other _ (by decide), q16]) (fun j hj => (hL j hj).2.2)
    fun t20 ht20 hv20 e20 w20 => WP.block_nil ⟨e, ?_,
      hv18.of (by rw [e20, e19]) (by rw [e20, e19]) (by rw [e20, e19]) (w20.trans w19)⟩
  -- the values
  have v5 : (t3.gpr .r5).toNat = (t.gpr .r5).toNat := by rw [g3 _ (by decide)]
  have v4 : (t4.gpr .r4).toNat = (t.gpr .r4).toNat := by rw [e4, g3 _ (by decide)]
  have v3 : (t5.gpr .r3).toNat = isqrt T := by rw [e5, e4, g3 _ (by decide), q3]
  have l5 := (t.gpr .r5).isLt
  have sl2 : isqrt T < 2 ^ 32 := sl
  have p32 : (2 : Nat) ^ (32 * 1) = 2 ^ 32 := rfl
  have eR' : setW (setW (AW σ wR) (P.W - 2) (t.gpr .r5).toNat) (P.W - 1) (t.gpr .r4).toNat =
      setWin (AW σ wR) (P.W - 2) 2 (T - isqrt T * isqrt T) := by
    rw [setW_eq_win, setW_eq_win, show P.W - 1 = P.W - 2 + 1 by omega, setWin_adj (by rw [p32]; exact l5), p32]
    congr 1; omega
  have eD' : setW (setW 0 (P.W / 2 - 1) (2 * isqrt T % 2 ^ 32)) (P.W / 2) (isqrt T / 2 ^ 31) =
      setWin 0 (P.W / 2 - 1) 2 (2 * isqrt T) := by
    obtain ⟨k, hk⟩ : ∃ k, P.W / 2 = k + 1 := ⟨P.W / 2 - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, setW_eq_win, setW_eq_win, setWin_adj (by rw [p32]; exact Nat.mod_lt _ (by decide)),
      p32]
    congr 1; omega
  have eE' : setW (setW (cmpl P.W 0) (P.W / 2 - 1) (2 ^ 32 - 1 - 2 * isqrt T % 2 ^ 32)) (P.W / 2)
      (2 ^ 32 - 1 - isqrt T / 2 ^ 31) = cmpl P.W (setWin 0 (P.W / 2 - 1) 2 (2 * isqrt T)) := by
    rw [← eD', cmpl_setW (by omega) (setW_lt (by omega) (Nat.two_pow_pos _) (Nat.mod_lt _ (by decide))) (by omega),
      cmpl_setW (by omega) (Nat.two_pow_pos _) (Nat.mod_lt _ (by decide))]
  refine ht20.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨hd, ?_⟩)
  · simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hj)))))
  · beta_reduce
    rw [eT]
    by_cases c1 : j = wE
    · subst c1
      simp only [upd_self, upd_ne _ _ (show wE ≠ wD by decide), upd_ne _ _ (show wE ≠ wR by decide)]
      rw [c0 σ e, e19, na, nb, eE']
    · by_cases c2 : j = wD
      · subst c2
        simp only [upd_self, upd_ne _ _ c1, upd_ne _ _ (show wD ≠ wR by decide)]
        rw [d0 σ e, e12, va, vb, eD']
      · by_cases c3 : j = wR
        · subst c3
          simp only [upd_self, upd_ne _ _ c1, upd_ne _ _ c2]
          rw [v5, v4, eR']
        · simp only [upd_ne _ _ c1, upd_ne _ _ c2, upd_ne _ _ c3]
  · beta_reduce
    rw [eT]
    by_cases cd : d = VG.Impl.Rsa.Arm.KeyDiv.sD
    · subst cd; simp only [upd_self]; exact v3
    · simp only [upd_ne _ _ cd]

end

end VG.Proof.Rsa.Arm.RecoverDet
