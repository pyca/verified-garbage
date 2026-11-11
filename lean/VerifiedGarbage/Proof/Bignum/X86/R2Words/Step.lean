module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Add
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordStep32
import VerifiedGarbage.Proof.Bignum.WordStepNorm32

-- separate module: the word steps' proof is split in a chain of modules, so that a change rebuilds only the modules after it

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

/-- The top word `a₁` of `x` shifted, `a₁ 2^z < 2^32`, for `2^z x < 2^(32 (k + 3))`. -/
theorem top_small {L k a1 a2 a3 z : Nat}
    (htop : (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z < 2 ^ (32 * (k + 3))) :
    a1 * 2 ^ z < 2 ^ 32 := by
  have e : 2 ^ (32 * (k + 3)) = 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 * 2 ^ 32 := by
    rw [show 32 * (k + 3) = 32 * k + 32 + 32 + 32 by omega, Nat.pow_add, Nat.pow_add, Nat.pow_add]
  rw [e] at htop
  have h2 : 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 * (a1 * 2 ^ z) ≤
      (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z := by
    have : 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 * a1 ≤ L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1) := by
      rw [Nat.mul_add (2 ^ (32 * k) * 2 ^ 32), Nat.mul_assoc (2 ^ (32 * k) * 2 ^ 32) (2 ^ 32)]; omega
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ this
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h2 htop)

/-- The top three words `(u₂, u₁, u₀)` of `2^z x`, from `x`'s top four words
`a₁`, `a₂`, `a₃`, `a`, for `a₁ 2^z < 2^32`. -/
theorem top3_math {L k a a1 a2 a3 z : Nat} (hz : z ≤ 31) (hL : L < 2 ^ (32 * k)) (h1 : a1 * 2 ^ z < 2 ^ 32) :
    (a1 * 2 ^ z % 2 ^ 32 + a2 * 2 ^ z / 2 ^ 32) * 2 ^ 64 + (a2 * 2 ^ z % 2 ^ 32 + a3 * 2 ^ z / 2 ^ 32) * 2 ^ 32 +
        (a3 * 2 ^ z % 2 ^ 32 + a * 2 ^ z / 2 ^ 32) =
      (L + 2 ^ (32 * k) * a + 2 ^ (32 * k) * 2 ^ 32 * (a3 + 2 ^ 32 * a2 + 2 ^ 64 * a1)) * 2 ^ z /
        (2 ^ (32 * k) * 2 ^ 32) := by
  have e : (a3 + 2 ^ 32 * a2 + 2 ^ 64 * a1) * 2 ^ z = a3 * 2 ^ z + 2 ^ 32 * (a2 * 2 ^ z) + 2 ^ 64 * (a1 * 2 ^ z) := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  rw [shl_div (by omega) hL, e, Nat.mod_eq_of_lt h1]
  have h2 := Nat.div_add_mod (a2 * 2 ^ z) (2 ^ 32)
  have h3 := Nat.div_add_mod (a3 * 2 ^ z) (2 ^ 32)
  generalize a * 2 ^ z / 2 ^ 32 = hA
  generalize a1 * 2 ^ z = A1 at *
  generalize a2 * 2 ^ z = A2 at *
  generalize a3 * 2 ^ z = A3 at *
  omega

/-- The top two words `u₂ 2^32 + u₁` of `2^z x`, from `x`'s top three words
`a₁`, `a₂`, `a₃`, for `2^z x < 2^(32 (k + 3))`. -/
theorem top_math {L k a1 a2 a3 z : Nat} (hz : z ≤ 31) (hL : L < 2 ^ (32 * k))
    (htop : (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z < 2 ^ (32 * (k + 3))) :
    (a1 * 2 ^ z % 2 ^ 32 + a2 * 2 ^ z / 2 ^ 32) * 2 ^ 32 + (a2 * 2 ^ z % 2 ^ 32 + a3 * 2 ^ z / 2 ^ 32) =
      (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z / 2 ^ (32 * (k + 1)) := by
  have hK := Nat.two_pow_pos (32 * k)
  rw [show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add, shl_div (by omega) hL]
  have h1 : a1 * 2 ^ z < 2 ^ 32 := top_small htop
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
the header below 172, the words from 192 to number 4, and number 4's words
from `W'` to number 5. -/
structure StepFrame (base : Addr) (len : Nat) (m m' : Mem) : Prop where
  out : Outside base oMask (numAt len 5 + 4 * (wp len + 1) - oMask) m m'
  mid : ∀ o, oU2 + 4 ≤ o → o + 4 ≤ numAt len 4 → w32 m' base o = w32 m base o
  up : ∀ o, numAt len 4 + 4 * wp len ≤ o → o + 4 ≤ numAt len 5 → w32 m' base o = w32 m base o
  steps : w32 m' base oSteps = w32 m base oSteps

/-- A step: `x := x 2^32 mod M`, for the header's `p = 2^z`, `d` and `d₁`
(`2^z M`'s top two words) and `v`. -/
theorem step_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {m x z : Nat}
    (h : PcIn base bytes len args s) (hz : z ≤ 31) (hP : w32 s.mem base oP = 2 ^ z)
    (hMw : m * 2 ^ z < 2 ^ (32 * wp len))
    (hD : w32 s.mem base oD = m * 2 ^ z / 2 ^ (32 * (wp len - 1)))
    (hd1 : 2 ^ 31 ≤ m * 2 ^ z / 2 ^ (32 * (wp len - 1)))
    (hD1 : w32 s.mem base oD1 = m * 2 ^ z / 2 ^ (32 * (wp len - 2)) % 2 ^ 32)
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
  have eT : ∀ i, i ≤ 4 → topW s.mem base len 4 i = w32 s.mem base (numAt len 4 + 4 * (k + 3 - i)) := fun i hi => by
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
  -- `u₀`, and the top three words `U` of `2^z x`.
  obtain ⟨u0, hu0⟩ : ∃ u0, u0 = topW s.mem base len 4 3 * 2 ^ z % 2 ^ 32 + topW s.mem base len 4 4 * 2 ^ z / 2 ^ 32 :=
    ⟨_, rfl⟩
  have hu0' : u0 < 2 ^ 32 := by rw [hu0]; exact lohi_lt (by omega) (s.mem.readW _ 32).isLt
  have hU3 : u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 = x * 2 ^ z / 2 ^ (32 * (wp len - 3)) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have i1 : k' + 1 + 3 - 1 = k' + 1 + 2 := by omega
    have i2 : k' + 1 + 3 - 2 = k' + 1 + 1 := by omega
    have i3 : k' + 1 + 3 - 3 = k' + 1 := by omega
    have i4 : k' + 1 + 3 - 4 = k' := by omega
    have hxe : x = val32 s.mem base (numAt len 4) k' + 2 ^ (32 * k') * topW s.mem base len 4 4 +
        2 ^ (32 * k') * 2 ^ 32 * (topW s.mem base len 4 3 + 2 ^ 32 * topW s.mem base len 4 2 +
          2 ^ 64 * topW s.mem base len 4 1) := by
      rw [eT 1 (by omega), eT 2 (by omega), eT 3 (by omega), eT 4 (by omega), i1, i2, i3, i4, hx3, val32_succ,
        show 32 * (k' + 1) = 32 * k' + 32 by omega, Nat.pow_add]
      grind
    have hsmall := top_small (L := val32 s.mem base (numAt len 4) (k' + 1)) (k := k' + 1)
      (a1 := topW s.mem base len 4 1) (a2 := topW s.mem base len 4 2) (a3 := topW s.mem base len 4 3) (z := z) (by
        rw [eT 1 (by omega), eT 2 (by omega), eT 3 (by omega), i1, i2, i3, ← hx3, ← hk]; exact hxz)
    rw [hu2, hu1, hu0, top3_math (L := val32 s.mem base (numAt len 4) k') (k := k') hz (val32_lt _ _ _ _) hsmall,
      show 32 * (wp len - 3) = 32 * k' + 32 by omega, Nat.pow_add, ← hxe]
  -- The top two words `D = (d, d₁)` of `2^z M`.
  have hDd : d * 2 ^ 32 + w32 s.mem base oD1 = m * 2 ^ z / 2 ^ (32 * (wp len - 2)) := by
    rw [hD1, hdd, show 32 * (wp len - 1) = 32 * (wp len - 2) + 32 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    exact Nat.div_add_mod' _ _
  obtain ⟨hUD, hq1, hq2, hge, hle⟩ := VG.Proof.Bignum.WordStep32.qhat3_norm (X := x) (M := m) (P := 2 ^ z)
    (K := 32 * (wp len - 3)) hz0 hxm (by
      rw [show 32 * (wp len - 3) + 32 = 32 * (wp len - 2) by omega, ← hDd]
      rw [show (d * 2 ^ 32 + w32 s.mem base oD1) / 2 ^ 32 = d by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt (s.mem.readW _ 32).isLt, Nat.zero_add]]
      exact hd1)
  rw [← hU3, show 32 * (wp len - 3) + 32 = 32 * (wp len - 2) by omega, ← hDd] at hUD hq1 hq2 hge hle
  rw [show (u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / 2 ^ 32 = u2 * 2 ^ 32 + u1 by
      rw [show u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 = (u2 * 2 ^ 32 + u1) * 2 ^ 32 + u0 by
        rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl]; grind,
        Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hu0', Nat.zero_add],
    show (d * 2 ^ 32 + w32 s.mem base oD1) / 2 ^ 32 = d by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt (s.mem.readW _ 32).isLt, Nat.zero_add]]
    at hq1 hq2
  -- `top`, `quot` and `refine3`.
  unfold step
  simp only [seqs, List.append_assoc]
  refine WP.seq (top_ok h fun t₁ K₁ m₁ bp₁ ax₁ => ?_)
  rw [hP, ← hu1] at bp₁
  rw [hP, ← hu2] at ax₁
  rw [hP, ← hu0, ← hu2] at m₁
  have O₁ : Outside base oU0 8 s.mem t₁.mem := by
    rw [m₁]
    exact ((writeW32_outside _ base _ (d := oU0) (by simp only [oU0]; omega)).mono (by omega) (by simp only [oU0]; omega)).trans
      ((writeW32_outside _ base _ (d := oU2) (by simp only [oU2]; omega)).mono (by simp only [oU0, oU2]; omega)
        (by simp only [oU0, oU2]; omega))
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (by omega) (by simp only [oU0]; omega))
  have di₁ : PtrAt t₁ base .edi 0 := by rw [PtrAt, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; exact h₁.edi
  have w₁ : ∀ o, o + 4 ≤ oU0 → w32 t₁.mem base o = w32 s.mem base o := fun o ho =>
    O₁.w32 (d := o) (.inl ho) (by simp only [oU0] at ho; omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keeps [.eax, .ebx, .ecx, .edx, .esi] (quot_ok h₁.ws di₁ (by omega) ax₁ bp₁
    (by rw [w₁ _ (by simp only [oD, oU0]; omega)]; exact hD) (by rw [w₁ _ (by simp only [oV, oU0]; omega)]; exact hV)
    hd1 hd2 hud hu1') rfl) fun s₁ ⟨⟨hq₁, O₁', C₁, K₁'⟩, KK⟩ => ?_
  rw [qhat_min hud hu1' (by omega)] at hq₁
  have bp₂ : s₁.gpr .ebp = BitVec.ofNat 32 u1 := (KK.1 _ (by decide)).trans bp₁
  have K₀₁ : Keeps k6 s s₁ := K₁.trans K₁'
  have O₀₁ : Outside base oMask 20 s.mem s₁.mem :=
    (O₁.mono (by simp only [oMask, oU0]; omega) (by simp only [oMask, oU0]; omega)).trans
      (O₁'.mono (by omega) (by simp only [oMask]; omega))
  have hs₁ := h.keep K₀₁ (by decide) (by decide) (O₀₁.mono (by omega) (by simp only [oMask]; omega))
  have di₂ : PtrAt s₁ base .edi 0 := by rw [PtrAt, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; exact hs₁.edi
  -- `s₁`'s header words.
  have wU0 : w32 s₁.mem base oU0 = u0 := by
    rw [O₁'.w32 (d := oU0) (.inr (by simp only [oMask, oU0]; omega)) (by simp only [oU0]; omega), m₁,
      (writeW32_outside _ base _ (d := oU2) (by simp only [oU2]; omega)).w32 (d := oU0) (.inl (by simp only [oU0, oU2]; omega))
        (by simp only [oU0]; omega), w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu0']
  have wU2 : w32 s₁.mem base oU2 = u2 := by
    rw [O₁'.w32 (d := oU2) (.inr (by simp only [oMask, oU2]; omega)) (by simp only [oU2]; omega), m₁, w32_write_self,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu2']
  have wD : w32 s₁.mem base oD = d := by
    rw [O₀₁.w32 (d := oD) (.inl (by simp only [oD, oMask]; omega)) (by simp only [oD]; omega), hD]
  have wD1 : w32 s₁.mem base oD1 = w32 s.mem base oD1 := O₀₁.w32 (d := oD1) (.inr (by simp only [oD1, oMask]; omega))
    (by simp only [oD1]; omega)
  refine WP.mono (refine3_ok hs₁.ws di₂ (by omega) (U := u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0)
    (D := d * 2 ^ 32 + w32 s.mem base oD1)
    (by rw [wU2, bp₂, wU0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu1']) (by rw [wD, wD1])
    (by omega) hUD (by rw [hq₁]; exact hq1) (by rw [hq₁]; exact hq2)) fun s₂ ⟨m₂, K₂⟩ => ?_
  generalize hQ : min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (d * 2 ^ 32 + w32 s.mem base oD1)) (2 ^ 32 - 1) = Q
    at m₂ hge hle
  have hQlt : Q < 2 ^ 32 := by rw [← hQ]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have O₂ : Outside base oQ 4 s₁.mem s₂.mem := by rw [m₂]; exact writeW32_outside _ base _ (by simp only [oQ]; omega)
  have hs₂ := hs₁.keep K₂ (by decide) (by decide) (O₂.mono (by omega) (by simp only [oQ]; omega))
  have wQ : w32 s₂.mem base oQ = Q := by rw [m₂, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hQlt]
  have M₂ : val32 s₂.mem base (numAt len 0) (wp len) = m := by
    rw [O₂.val32 (.inr (by simp only [oQ]; omega)) (by omega), O₀₁.val32 (.inr (by simp only [oMask]; omega)) (by omega), hM]
  have X₂ : val32 s₂.mem base (numAt len 4) (wp len) = x := by
    rw [O₂.val32 (.inr (by simp only [oQ]; omega)) (by omega), O₀₁.val32 (.inr (by simp only [oMask]; omega)) (by omega), hx]
  -- `t = x 2^32 - Q M`.
  refine WP.seq (WP.mono (mulSub_ok hs₂) fun s₃ ⟨b, hb, hv₃, O₃, K₃⟩ => ?_)
  rw [wQ, M₂, X₂] at hv₃
  have hs₃ := hs₂.keep K₃ (by decide) (by decide) (O₃.mono (by omega) (by omega))
  have M₃ : val32 s₃.mem base (numAt len 0) (wp len) = m := by
    rw [O₃.val32 (.inl (by omega)) (by omega), M₂]
  -- `t := t + M` if `t < 0`.
  refine WP.seq (WP.mono (addBack_ok hs₃) fun s₄ ⟨c1, hc1, hv₄, O₄, K₄⟩ => ?_)
  have hs₄ := hs₃.keep K₄ (by decide) (by decide) (O₄.mono (by omega) (by omega))
  rw [M₃] at hv₄
  have tb : ∀ mm : Mem, (2 ^ 31 ≤ w32 mm base (numAt len 5 + 4 * wp len)) ↔
      2 ^ (32 * (wp len + 1)) / 2 ≤ val32 mm base (numAt len 5) (wp len + 1) := fun mm => by
    rw [val32_succ]; exact (topBit_iff (val32_lt _ _ _ _) (mm.readW _ 32).isLt).symm
  have hv₄' : val32 s₄.mem base (numAt len 5) (wp len + 1) + 2 ^ (32 * (wp len + 1)) * c1 =
      val32 s₃.mem base (numAt len 5) (wp len + 1) +
        if 2 ^ (32 * (wp len + 1)) / 2 ≤ val32 s₃.mem base (numAt len 5) (wp len + 1) then m else 0 := by
    simp only [tb] at hv₄; exact hv₄
  have hm32 : m < 2 ^ (32 * wp len) := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hz0) hMw
  have hMW : 2 * m < 2 ^ (32 * (wp len + 1)) / 2 := by
    rw [show 32 * (wp len + 1) = 32 * wp len + 32 by omega, Nat.pow_add]; omega
  have hT := VG.Proof.Bignum.WordStep32.wordStepQ1_val (by omega) hMW hge hle (val32_lt _ _ _ _) hb hv₃
    (val32_lt _ _ _ _) hc1 hv₄'
  -- `t` back into `x`.
  refine WP.mono (copyBack_ok hs₄) fun s₅ ⟨hv₅, O₅, K₅⟩ => ?_
  refine ⟨?_, ⟨?_, fun o h1 h2 => ?_, fun o h1 h2 => ?_, ?_⟩, K₀₁.trans (K₂.trans (K₃.trans (K₄.trans K₅)))⟩
  · rw [hv₅, ← hT, val32_succ]
    have hr : x * 2 ^ 32 % m < 2 ^ (32 * wp len) := Nat.lt_trans (Nat.mod_lt _ (by omega)) hm32
    rw [← hT, val32_succ] at hr
    have : w32 s₄.mem base (numAt len 5 + 4 * wp len) = 0 := by
      by_contra hc
      have := Nat.mul_le_mul_left (2 ^ (32 * wp len)) (show 1 ≤ w32 s₄.mem base (numAt len 5 + 4 * wp len) by omega)
      omega
    rw [this, Nat.mul_zero, Nat.add_zero]
  · exact ((((O₀₁.mono (by omega) (by simp only [oMask]; omega)).trans (O₂.mono (by simp only [oMask, oQ]; omega)
      (by simp only [oMask, oQ]; omega))).trans (O₃.mono (by simp only [oMask]; omega) (by simp only [oMask]; omega))).trans
      (O₄.mono (by simp only [oMask]; omega) (by simp only [oMask]; omega))).trans
      (O₅.mono (by simp only [oMask]; omega) (by simp only [oMask]; omega))
  · simp only [oU2] at h1
    rw [O₅.w32 (d := o) (.inl (by omega)) (by omega), O₄.w32 (d := o) (.inl (by omega)) (by omega),
      O₃.w32 (d := o) (.inl (by omega)) (by omega), O₂.w32 (d := o) (.inr (by simp only [oQ]; omega)) (by omega),
      O₀₁.w32 (d := o) (.inr (by simp only [oMask]; omega)) (by omega)]
  · rw [O₅.w32 (d := o) (.inr (by omega)) (by omega), O₄.w32 (d := o) (.inl (by omega)) (by omega),
      O₃.w32 (d := o) (.inl (by omega)) (by omega), O₂.w32 (d := o) (.inr (by simp only [oQ]; omega)) (by omega),
      O₀₁.w32 (d := o) (.inr (by simp only [oMask]; omega)) (by omega)]
  · rw [O₅.w32 (d := oSteps) (.inl (by simp only [oSteps]; omega)) (by simp only [oSteps]; omega),
      O₄.w32 (d := oSteps) (.inl (by simp only [oSteps]; omega)) (by simp only [oSteps]; omega),
      O₃.w32 (d := oSteps) (.inl (by simp only [oSteps]; omega)) (by simp only [oSteps]; omega),
      O₂.w32 (d := oSteps) (.inl (by simp only [oSteps, oQ]; omega)) (by simp only [oSteps]; omega), C₁,
      O₁.w32 (d := oSteps) (.inl (by simp only [oSteps, oU0]; omega)) (by simp only [oSteps]; omega)]
end VG.Proof.Bignum.X86.R2Words
