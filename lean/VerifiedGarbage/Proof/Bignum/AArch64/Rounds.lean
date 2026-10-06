import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.Math

/-!
# Multiword arithmetic on AArch64: the rounds of Montgomery multiplication

`zeroAcc` clears the accumulator (`zeroAcc_ok`); `round` is one round of
CIOS, `T := (T + a_i B + u m) / 2⁶⁴` (`round_ok`); `rounds` runs them for
`i = 0, …, w - 1` (`rounds_ok`): the accumulator ends below `2m` and
congruent to `a B R⁻¹` modulo `m`.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-! ## Clearing the accumulator -/

structure ZeroInv (s : State) (B : Addr) (Z eA : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x14, .x16] s t
  x16 : t.gpr .x16 = off B (eA + 8 * j)
  out : Outside B eA (8 * j) s.mem t.mem
  val : wv t.mem B eA j = 0

theorem zeroAcc_ok {s : State} {B : Addr} {Z w eA : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0)
    (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 2) ≤ Z) :
    WP isa zeroAcc s fun t => wv t.mem B eA (w + 2) = 0 ∧ Outside B eA (8 * (w + 2)) s.mem t.mem ∧
      Keep [.x14, .x16] s t := by
  have hn := hs.nowrap
  unfold zeroAcc
  refine WP.seq (WP.mono (WP.keep [.x14, .x16] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x14 = BitVec.ofNat 64 (w + 2) ∧ t.mem = s.mem)
    (by brun [h8, h12, ofNat_add_ofNat]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h14, hm₁⟩, k₁⟩ => ?_)
  have hstep : ∀ j < w + 2, ∀ t, ZeroInv s B Z eA j t → t.gpr .x14 = BitVec.ofNat 64 (w + 2 - j) →
      WP isa (.block ([st .x7 .x16, next .x16] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
        fun t' => ZeroInv s B Z eA (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
    intro j hj t hI _
    have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.x16] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eA + 8 * j)) (0 : BitVec 64) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8))
      (by brun [hI.x16, t7, hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)]) (by decide) (by decide)
        (by decide +kernel)) fun t₁ ⟨⟨hm, h16'⟩, k₁⟩ => ?_
    refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', _⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
    refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
      by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
    · rw [hm', hm]
      intro x hx
      rw [writeW_outside t.mem B _ (by omega) x (by omega)]
      exact hI.out x (by omega)
    · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hI.val]
      rfl
  refine WP.mono (wp_countdown (N := w + 2) (by omega) (by omega) (ZeroInv s B Z eA) hstep
    ⟨hs.congr k₁.wr, k₁.mono (by decide), by rw [h16]; rfl, by rw [hm₁]; exact Outside.refl _ _ _ _, rfl⟩ h14)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ## A round -/

/-- A round: `x1 := a_i` (`x11` advanced), `T += a_i B`, `T := (T + u m) / 2⁶⁴`. -/
theorem round_ok {s : State} {B : Addr} {Z w eA eb eN ea i : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h9 : s.gpr .x9 = off B eb) (h10 : s.gpr .x10 = off B eN)
    (h11 : s.gpr .x11 = off B (ea + 8 * i)) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0)
    (hi : i < w) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (ha : ea + 8 * w ≤ Z)
    (sb : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA) (sN : eA + 8 * (w + 2) ≤ eN ∨ eN + 8 * w ≤ eA)
    (sa : eA + 8 * (w + 2) ≤ ea ∨ ea + 8 * w ≤ eA)
    (hinv : ((word s.mem B eN).toNat * (s.gpr .x15).toNat + 1) % 2 ^ 64 = 0)
    (hT : wv s.mem B eA (w + 2) < 2 * wv s.mem B eN w) (hB : wv s.mem B eb w < wv s.mem B eN w) :
    WP isa round s fun t =>
      (∃ u < 2 ^ 64, 2 ^ 64 * wv t.mem B eA (w + 2) = wv s.mem B eA (w + 2) +
        (word s.mem B (ea + 8 * i)).toNat * wv s.mem B eb w + u * wv s.mem B eN w) ∧
      Outside B eA (8 * (w + 2)) s.mem t.mem ∧ t.gpr .x11 = off B (ea + 8 * (i + 1)) ∧
      Keep [.x1, .x2, .x3, .x4, .x11, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  have hNw : wv s.mem B eN w < 2 ^ (64 * w) := wv_lt _ _ _ _
  unfold round
  refine WP.seq (WP.mono (WP.keep [.x1, .x11] (Q := fun t => t.gpr .x1 = word s.mem B (ea + 8 * i) ∧
    t.gpr .x11 = off B (ea + 8 * (i + 1)) ∧ t.mem = s.mem)
    (by brun [h11, hs.ld (show ea + 8 * i + 8 ≤ Z by omega), Nat.mul_succ, Nat.add_assoc])
    (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨hcx, h11', hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  have hai := (word s.mem B (ea + 8 * i)).isLt
  have hbB : (word s.mem B (ea + 8 * i)).toNat * wv s.mem B eb w ≤ (2 ^ 64 - 1) * wv s.mem B eN w :=
    Nat.mul_le_mul (by omega) (by omega)
  refine WP.seq (WP.mono (mulAddRow_ok hs₁ ((k₁.gpr .x8 (by decide)).trans h8)
    ((k₁.gpr .x9 (by decide)).trans h9) ((k₁.gpr .x12 (by decide)).trans h12)
    ((k₁.gpr .x7 (by decide)).trans h7) (by omega) hw' hA hb sb (by
      rw [hm₁, hcx]
      have : 2 ^ (64 * (w + 2)) = 2 ^ 128 * 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega
      rw [this, Nat.sub_mul, Nat.one_mul] at *
      omega)) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  rw [hm₁, hcx] at hv₂
  rw [hm₁] at ho₂
  have hNeq : wv s₂.mem B eN w = wv s.mem B eN w := ho₂.wv (by omega) (by omega)
  have hN0 : word s₂.mem B eN = word s.mem B eN := ho₂.word (by omega) (by omega)
  have hs₂ := hs₁.congr k₂.wr
  have k12 := (k₁.trans k₂)
  refine WP.mono (reduceRow_ok hs₂ ((k12.gpr .x8 (by decide)).trans h8) ((k12.gpr .x10 (by decide)).trans h10)
    ((k12.gpr .x12 (by decide)).trans h12) ((k12.gpr .x7 (by decide)).trans h7) hw hw' hA hN sN (by
      rw [hN0, (k12.gpr .x15 (by decide) : s₂.gpr .x15 = s.gpr .x15)]; exact hinv) (by
      intro u hu
      rw [hv₂, hNeq]
      have hu' : u * wv s.mem B eN w ≤ (2 ^ 64 - 1) * wv s.mem B eN w := Nat.mul_le_mul_right _ (by omega)
      have : 2 ^ (64 * (w + 2)) = 2 ^ 128 * 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega
      rw [this]
      rw [Nat.sub_mul, Nat.one_mul] at hbB hu'
      have : 4 * 2 ^ (64 * w) ≤ 2 ^ 128 * 2 ^ (64 * w) - 2 ^ 66 * 2 ^ (64 * w) := by
        rw [← Nat.sub_mul]; exact Nat.mul_le_mul_right _ (by decide)
      omega)) fun t ⟨hv, ho, k₃⟩ => ?_
  refine ⟨⟨(word s₂.mem B eA).toNat * (s₂.gpr .x15).toNat % 2 ^ 64, Nat.mod_lt _ (by decide), ?_⟩,
    ho₂.trans ho, by rw [k₃.gpr .x11 (by decide), k₂.gpr .x11 (by decide), h11'],
    (k12.trans k₃).mono (by decide)⟩
  rw [hv, hv₂, hNeq]

/-! ## The rounds -/

/-- After rounds `0, …, i - 1` from `s₀`: the accumulator `T < 2m` and
`2^(64 i) T ≡ (a mod 2^(64 i)) B (mod m)`. -/
structure RoundsInv (s₀ : State) (B : Addr) (Z w eA eb eN ea : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x4, .x11, .x13, .x14, .x16, .x17] s₀ t
  x11 : t.gpr .x11 = off B (ea + 8 * i)
  out : Outside B eA (8 * (w + 2)) s₀.mem t.mem
  lt : wv t.mem B eA (w + 2) < 2 * wv s₀.mem B eN w
  cong : 2 ^ (64 * i) * wv t.mem B eA (w + 2) % wv s₀.mem B eN w =
    wv s₀.mem B ea i * wv s₀.mem B eb w % wv s₀.mem B eN w

theorem rounds_ok {s : State} {B : Addr} {Z w eA eb eN ea : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h9 : s.gpr .x9 = off B eb) (h10 : s.gpr .x10 = off B eN)
    (h11 : s.gpr .x11 = off B ea) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (ha : ea + 8 * w ≤ Z)
    (sb : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA) (sN : eA + 8 * (w + 2) ≤ eN ∨ eN + 8 * w ≤ eA)
    (sa : eA + 8 * (w + 2) ≤ ea ∨ ea + 8 * w ≤ eA)
    (hinv : ((word s.mem B eN).toNat * (s.gpr .x15).toNat + 1) % 2 ^ 64 = 0)
    (h0 : wv s.mem B eA (w + 2) = 0) (hB : wv s.mem B eb w < wv s.mem B eN w) :
    WP isa rounds s (RoundsInv s B Z w eA eb eN ea w) := by
  have hn := hs.nowrap
  have hN0 : 0 < wv s.mem B eN w := by omega
  unfold rounds
  refine WP.seq (WP.mono (WP.keep [.x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by brun [h12]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h13, hm₁⟩, k₁⟩ => ?_)
  refine wp_countdown (N := w) (by omega) (by omega) (RoundsInv s B Z w eA eb eN ea) ?_
    ⟨hs.congr k₁.wr, k₁.mono (by decide), by rw [k₁.gpr .x11 (by decide), h11]; rfl,
      by rw [hm₁]; exact Outside.refl _ _ _ _, by rw [hm₁, h0]; omega, by rw [hm₁, h0]; simp [wv]⟩ h13
  intro i hi t hI _
  have hk := hI.keep
  have frame : ∀ {d k}, d + 8 * k ≤ Z → (d + 8 * k ≤ eA ∨ eA + 8 * (w + 2) ≤ d) →
      wv t.mem B d k = wv s.mem B d k := fun h1 h2 => hI.out.wv h2 (by omega)
  refine WP.seq (WP.mono (round_ok hI.scr ((hk.gpr .x8 (by decide)).trans h8) ((hk.gpr .x9 (by decide)).trans h9)
    ((hk.gpr .x10 (by decide)).trans h10) hI.x11 ((hk.gpr .x12 (by decide)).trans h12)
    ((hk.gpr .x7 (by decide)).trans h7) hi hw hw' hA hb hN ha sb sN sa (by
      rw [hI.out.word (by omega) (by omega), (hk.gpr .x15 (by decide) : t.gpr .x15 = s.gpr .x15)]; exact hinv)
    (by rw [frame hN (by omega)]; exact hI.lt) (by rw [frame hb (by omega), frame hN (by omega)]; exact hB))
    fun t₁ ⟨⟨u, hu, hv⟩, ho, h11', k₁'⟩ => ?_)
  refine WP.mono (dec_ok t₁ .x13) fun t' ⟨⟨h13', hm', _⟩, k'⟩ => ⟨?_, by rw [h13', k₁'.gpr .x13 (by decide)]⟩
  rw [frame hN (by omega), frame hb (by omega)] at hv
  have hai : (word t.mem B (ea + 8 * i)).toNat = (word s.mem B (ea + 8 * i)).toNat := by
    rw [hI.out.word (by omega) (by omega)]
  rw [hai] at hv
  refine ⟨hI.scr.congr (k'.wr.trans k₁'.wr), ((hk.trans k₁').trans k').mono (by decide),
    by rw [k'.gpr .x11 (by decide), h11'], by rw [hm']; exact hI.out.trans ho, ?_, ?_⟩
  · rw [hm']
    exact VG.Proof.Bignum.round_lt hv hI.lt (word s.mem B (ea + 8 * i)).isLt hB hu
  · rw [hm', show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add,
      VG.Proof.Bignum.round_step hv hI.cong]
    congr 1

end VG.Proof.Bignum.AArch64
