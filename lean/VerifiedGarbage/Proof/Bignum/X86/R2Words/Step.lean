module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Add
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordStep32

/-!
# `R2Words` on x86: a step `x := x 2^32 mod M`

From `p = 2^z`, `d`, `v` in the header and `x < M` in number 4, `step`
leaves `x 2^32 mod M` there (`step_ok`), by Knuth's step of long division
with the estimate from the normalized numbers `2^z x` and `2^z M`
(`WordStep32.wordStepNorm_val`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.PublicRt VG.Impl.Bignum.X86.R2Words VG.Proof.Bignum.X86.PrecomputeRt
open VG.Proof.Bignum.WordStep32

/-- A number of `k + 3` words as its top three words and the rest. -/
theorem val32_top3 (m : Mem) (base : Addr) (o k : Nat) :
    val32 m base o (k + 3) = val32 m base o k + 2 ^ (32 * k) * w32 m base (o + 4 * k) +
      2 ^ (32 * k) * 2 ^ 32 * (w32 m base (o + 4 * (k + 1)) + 2 ^ 32 * w32 m base (o + 4 * (k + 2))) := by
  rw [show k + 3 = k + 1 + 1 + 1 from rfl, val32_succ, val32_succ, val32_succ,
    show 32 * (k + 1 + 1) = 32 * k + 32 + 32 by omega, show 32 * (k + 1) = 32 * k + 32 by omega,
    Nat.pow_add, Nat.pow_add, show k + 1 + 1 = k + 2 from rfl]
  grind

/-- A number of `k + 2` words as its top two words and the rest. -/
theorem val32_top2 (m : Mem) (base : Addr) (o k : Nat) :
    val32 m base o (k + 2) = val32 m base o k + 2 ^ (32 * k) * (w32 m base (o + 4 * k) +
      2 ^ 32 * w32 m base (o + 4 * (k + 1))) := by
  rw [show k + 2 = k + 1 + 1 from rfl, val32_succ, val32_succ, show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add]
  grind

/-- The top two words `u₂ 2^32 + u₁` of `2^z x`, from `x`'s top three words
`a₁`, `a₂`, `a₃`, for `2^z x < 2^(32 (k + 3))`. -/
theorem top_math {L k a1 a2 a3 z : Nat} (hz : z ≤ 31) (hL : L < 2 ^ (32 * k))
    (htop : (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z < 2 ^ (32 * (k + 3))) :
    (a1 * 2 ^ z % 2 ^ 32 + a2 * 2 ^ z / 2 ^ 32) * 2 ^ 32 + (a2 * 2 ^ z % 2 ^ 32 + a3 * 2 ^ z / 2 ^ 32) =
      (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z / 2 ^ (32 * (k + 1)) := by
  have hK := Nat.two_pow_pos (32 * k)
  rw [show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add, shl_div (by omega) hL]
  -- `a₁ 2^z < 2^32`.
  have h1 : a1 * 2 ^ z < 2 ^ 32 := by
    have e : 2 ^ (32 * (k + 3)) = 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 * 2 ^ 32 := by
      rw [show 32 * (k + 3) = 32 * k + 32 + 32 + 32 by omega, Nat.pow_add, Nat.pow_add, Nat.pow_add]
    rw [e] at htop
    have h2 : 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 * (a1 * 2 ^ z) ≤
        (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z := by
      have : 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 * a1 ≤ L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1) := by
        rw [Nat.mul_add (2 ^ (32 * k) * 2 ^ 32), Nat.mul_assoc (2 ^ (32 * k) * 2 ^ 32) (2 ^ 32)]; omega
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ this
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h2 htop)
  have hd := Nat.div_add_mod (a2 * 2 ^ z) (2 ^ 32)
  rw [Nat.mod_eq_of_lt h1]
  grind

/-- The top bit of a number of `w + 1` words. -/
theorem topBit_iff {low top w : Nat} (hl : low < 2 ^ (32 * w)) (ht : top < 2 ^ 32) :
    (2 ^ (32 * (w + 1)) / 2 ≤ low + 2 ^ (32 * w) * top) ↔ 2 ^ 31 ≤ top := by
  have e : 2 ^ (32 * (w + 1)) / 2 = 2 ^ (32 * w) * 2 ^ 31 := by
    rw [show 32 * (w + 1) = 32 * w + 31 + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide), Nat.pow_add]
  rw [e]
  constructor
  · intro h
    by_contra hc
    have := Nat.mul_le_mul_left (2 ^ (32 * w)) (show top + 1 ≤ 2 ^ 31 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · intro h; have := Nat.mul_le_mul_left (2 ^ (32 * w)) h; omega

/-- `quot`'s estimate is `min(⌊(u₂ 2^32 + u₁) / d⌋, 2^32 - 1)`. -/
theorem qhat_min {u2 u1 d : Nat} (hu : u2 ≤ d) (hu1 : u1 < 2 ^ 32) (hd : 0 < d) :
    (if u2 = d then 2 ^ 32 - 1 else (u2 * 2 ^ 32 + u1) / d) = min ((u2 * 2 ^ 32 + u1) / d) (2 ^ 32 - 1) := by
  by_cases e : u2 = d
  · rw [ite_eq_left e, Nat.min_eq_right]
    rw [e, Nat.le_div_iff_mul_le hd]
    have : (2 ^ 32 - 1) * d ≤ 2 ^ 32 * d := Nat.mul_le_mul_right d (Nat.sub_le _ _)
    rw [Nat.mul_comm d]; omega
  · rw [ite_eq_right e, Nat.min_eq_left]
    have : (u2 * 2 ^ 32 + u1) / d < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul hd]
      have := Nat.mul_le_mul_right (2 ^ 32) (show u2 + 1 ≤ d by omega)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm d] at this; omega
    omega

/-- What a step leaves of the memory: everything outside `[172, t + 4 (W' + 1))`,
the header below 172, the words from 184 to number 4, and number 4's words
from `W'` to number 5. -/
structure StepFrame (base : Addr) (len : Nat) (m m' : Mem) : Prop where
  out : Outside base oMask (numAt len 5 + 4 * (wp len + 1) - oMask) m m'
  mid : ∀ o, oQ + 4 ≤ o → o + 4 ≤ numAt len 4 → w32 m' base o = w32 m base o
  up : ∀ o, numAt len 4 + 4 * wp len ≤ o → o + 4 ≤ numAt len 5 → w32 m' base o = w32 m base o
  steps : w32 m' base oSteps = w32 m base oSteps

/-- A step: `x := x 2^32 mod M`, for the header's `p = 2^z`, `d` (`2^z M`'s
top word) and `v`. -/
theorem step_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {m x z : Nat}
    (h : PcIn base bytes len args s) (hz : z ≤ 31) (hP : w32 s.mem base oP = 2 ^ z)
    (hMw : m * 2 ^ z < 2 ^ (32 * wp len))
    (hD : w32 s.mem base oD = m * 2 ^ z / 2 ^ (32 * (wp len - 1)))
    (hd1 : 2 ^ 31 ≤ m * 2 ^ z / 2 ^ (32 * (wp len - 1)))
    (hV : w32 s.mem base oV = (2 ^ 64 - 1) / (m * 2 ^ z / 2 ^ (32 * (wp len - 1))) - 2 ^ 32)
    (hM : val32 s.mem base (numAt len 0) (wp len) = m)
    (hx : val32 s.mem base (numAt len 4) (wp len) = x) (hxm : x < m) :
    WP isa step s fun t => val32 t.mem base (numAt len 4) (wp len) = x * 2 ^ 32 % m ∧
      StepFrame base len s.mem t.mem ∧ Keeps k6 s t := by
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have hl := h.lower
  have hwp16 : 16 ≤ wp len := by simp only [wp]; omega
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  obtain ⟨d, hdd⟩ : ∃ d, d = m * 2 ^ z / 2 ^ (32 * (wp len - 1)) := ⟨_, rfl⟩
  rw [← hdd] at hD hd1 hV
  have hd2 : d < 2 ^ 32 := by
    rw [hdd, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show 32 + 32 * (wp len - 1) = 32 * wp len by omega]; exact hMw
  have hz0 := Nat.two_pow_pos z
  have hxz : x * 2 ^ z < 2 ^ (32 * wp len) := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hxm)) hMw
  -- `x`'s top three words.
  obtain ⟨k, hk⟩ : ∃ k, wp len = k + 3 := ⟨wp len - 3, by omega⟩
  have hx3 := val32_top3 s.mem base (numAt len 4) k
  rw [← hk, hx] at hx3
  have eT : ∀ i, i ≤ 3 → topW s.mem base len 4 i = w32 s.mem base (numAt len 4 + 4 * (k + 3 - i)) := fun i hi => by
    simp only [topW]; congr 1; omega
  obtain ⟨u2, hu2⟩ : ∃ u2, u2 = topW s.mem base len 4 1 * 2 ^ z % 2 ^ 32 + topW s.mem base len 4 2 * 2 ^ z / 2 ^ 32 :=
    ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1, u1 = topW s.mem base len 4 2 * 2 ^ z % 2 ^ 32 + topW s.mem base len 4 3 * 2 ^ z / 2 ^ 32 :=
    ⟨_, rfl⟩
  have hu1' : u1 < 2 ^ 32 := by rw [hu1]; exact lohi_lt (by omega) (s.mem.readW _ 32).isLt
  have hu2' : u2 < 2 ^ 32 := by rw [hu2]; exact lohi_lt (by omega) (s.mem.readW _ 32).isLt
  have hui : u2 * 2 ^ 32 + u1 = x * 2 ^ z / 2 ^ (32 * (wp len - 2)) := by
    rw [hu2, hu1, eT 1 (by omega), eT 2 (by omega), eT 3 (by omega), show k + 3 - 1 = k + 2 by omega,
      show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega, hx3, show wp len - 2 = k + 1 by omega]
    refine top_math hz (val32_lt _ _ _ _) ?_
    rw [← hx3, ← hk]; exact hxz
  have hud : u2 ≤ d := by
    have e1 : u2 = x * 2 ^ z / 2 ^ (32 * (wp len - 1)) := by
      rw [show 32 * (wp len - 1) = 32 * (wp len - 2) + 32 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul, ← hui]
      omega
    rw [e1, hdd]
    exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hxm))
  -- `top` and `quot`.
  unfold step
  simp only [seqs]
  refine WP.seq (top_ok h fun t₁ K₁ m₁ bp₁ ax₁ => ?_)
  rw [hP, ← hu1] at bp₁
  rw [hP, ← hu2] at ax₁
  have h₁ := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  have di₁ : PtrAt t₁ base .edi 0 := by rw [PtrAt, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; exact h₁.edi
  refine WP.mono (quot_ok h₁.ws di₁ (by omega) ax₁ bp₁ (by rw [m₁]; exact hD) (by rw [m₁]; exact hV) hd1 hd2 hud hu1')
    fun s₁ ⟨hq₁, O₁, C₁, K₁'⟩ => ?_
  rw [qhat_min hud hu1' (by omega)] at hq₁
  rw [m₁] at O₁
  have K₀₁ : Keeps k6 s s₁ := K₁.trans K₁'
  have hs₁ := h.keep K₀₁ (by decide) (by decide) (O₁.mono (by omega) (by simp only [oMask]; omega))
  have M₁ : val32 s₁.mem base (numAt len 0) (wp len) = m := by
    rw [O₁.val32 (.inr (by simp only [oMask]; omega)) (by omega), hM]
  have X₁ : val32 s₁.mem base (numAt len 4) (wp len) = x := by
    rw [O₁.val32 (.inr (by simp only [oMask]; omega)) (by omega), hx]
  -- `t = x 2^32 - q̂ M`.
  refine WP.seq (WP.mono (mulSub_ok hs₁) fun s₂ ⟨b, hb, hv₂, O₂, K₂⟩ => ?_)
  rw [hq₁, M₁, X₁] at hv₂
  have hs₂ := hs₁.keep K₂ (by decide) (by decide) (O₂.mono (by omega) (by omega))
  have M₂ : val32 s₂.mem base (numAt len 0) (wp len) = m := by
    rw [O₂.val32 (.inl (by omega)) (by omega), M₁]
  -- Twice `t := t + M` if `t < 0`.
  refine WP.seq (WP.mono (addBack_ok hs₂) fun s₃ ⟨c1, hc1, hv₃, O₃, K₃⟩ => ?_)
  have hs₃ := hs₂.keep K₃ (by decide) (by decide) (O₃.mono (by omega) (by omega))
  have M₃ : val32 s₃.mem base (numAt len 0) (wp len) = m := by
    rw [O₃.val32 (.inl (by omega)) (by omega), M₂]
  refine WP.seq (WP.mono (addBack_ok hs₃) fun s₄ ⟨c2, hc2, hv₄, O₄, K₄⟩ => ?_)
  have hs₄ := hs₃.keep K₄ (by decide) (by decide) (O₄.mono (by omega) (by omega))
  rw [M₂] at hv₃
  rw [M₃] at hv₄
  -- The top bits.
  have tb : ∀ mm : Mem, (2 ^ 31 ≤ w32 mm base (numAt len 5 + 4 * wp len)) ↔
      2 ^ (32 * (wp len + 1)) / 2 ≤ val32 mm base (numAt len 5) (wp len + 1) := fun mm => by
    rw [val32_succ]; exact (topBit_iff (val32_lt _ _ _ _) (mm.readW _ 32).isLt).symm
  have hv₃' : val32 s₃.mem base (numAt len 5) (wp len + 1) + 2 ^ (32 * (wp len + 1)) * c1 =
      val32 s₂.mem base (numAt len 5) (wp len + 1) +
        if 2 ^ (32 * (wp len + 1)) / 2 ≤ val32 s₂.mem base (numAt len 5) (wp len + 1) then m else 0 := by
    simp only [tb] at hv₃; exact hv₃
  have hv₄' : val32 s₄.mem base (numAt len 5) (wp len + 1) + 2 ^ (32 * (wp len + 1)) * c2 =
      val32 s₃.mem base (numAt len 5) (wp len + 1) +
        if 2 ^ (32 * (wp len + 1)) / 2 ≤ val32 s₃.mem base (numAt len 5) (wp len + 1) then m else 0 := by
    simp only [tb] at hv₄; exact hv₄
  have hT3 := wordStepNorm_val (w := wp len) (z := z) (x := x) (m := m) (by omega) rfl rfl
    (by rw [hui]) hdd hd1 hMw hxm (val32_lt _ _ _ _) hb hv₂ (val32_lt _ _ _ _) hc1 hv₃'
    (val32_lt _ _ _ _) hc2 hv₄'
  -- `t` back into `x`.
  refine WP.mono (copyBack_ok hs₄) fun s₅ ⟨hv₅, O₅, K₅⟩ => ?_
  have hm32 : m < 2 ^ (32 * wp len) := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hz0) hMw
  refine ⟨?_, ⟨?_, fun o h1 h2 => ?_, fun o h1 h2 => ?_, ?_⟩, K₀₁.trans (K₂.trans (K₃.trans (K₄.trans K₅)))⟩
  · rw [hv₅, ← hT3, val32_succ]
    have hr : x * 2 ^ 32 % m < 2 ^ (32 * wp len) := Nat.lt_trans (Nat.mod_lt _ (by omega)) hm32
    rw [← hT3, val32_succ] at hr
    have : w32 s₄.mem base (numAt len 5 + 4 * wp len) = 0 := by
      by_contra hc
      have := Nat.mul_le_mul_left (2 ^ (32 * wp len)) (show 1 ≤ w32 s₄.mem base (numAt len 5 + 4 * wp len) by omega)
      omega
    rw [this, Nat.mul_zero, Nat.add_zero]
  · exact (((O₁.mono (by omega) (by simp only [oMask]; omega)).trans (O₂.mono (by simp only [oMask]; omega)
      (by simp only [oMask]; omega))).trans ((O₃.mono (by simp only [oMask]; omega) (by simp only [oMask]; omega)).trans
      (O₄.mono (by simp only [oMask]; omega) (by simp only [oMask]; omega)))).trans
      (O₅.mono (by simp only [oMask]; omega) (by simp only [oMask]; omega))
  · simp only [oQ] at h1
    rw [O₅.w32 (.inl (by omega)) (by omega), O₄.w32 (.inl (by omega)) (by omega), O₃.w32 (.inl (by omega)) (by omega),
      O₂.w32 (.inl (by omega)) (by omega), O₁.w32 (.inr (by simp only [oMask]; omega)) (by omega)]
  · rw [O₅.w32 (.inr (by omega)) (by omega), O₄.w32 (.inl (by omega)) (by omega), O₃.w32 (.inl (by omega)) (by omega),
      O₂.w32 (.inl (by omega)) (by omega), O₁.w32 (.inr (by simp only [oMask]; omega)) (by omega)]

  · rw [O₅.w32 (.inl (by simp only [oSteps]; omega)) (by simp only [oSteps]; omega),
      O₄.w32 (.inl (by simp only [oSteps]; omega)) (by simp only [oSteps]; omega),
      O₃.w32 (.inl (by simp only [oSteps]; omega)) (by simp only [oSteps]; omega),
      O₂.w32 (.inl (by simp only [oSteps]; omega)) (by simp only [oSteps]; omega), C₁, m₁]

end VG.Proof.Bignum.X86.R2Words
