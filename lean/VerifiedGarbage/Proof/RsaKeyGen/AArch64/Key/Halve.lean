import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath

/-!
# An RSA key from its primes on AArch64: `φ` and the halving

`φ = (p − 1)(q − 1)` (`phi_k`), and a step of the halving of `u`, `v` and
`φ` while `u` and `v` are both even (`twoStep_k`, `halveStep`): the mask in
`x15`, and `halfIf` (`shr_ok` into `aT`, then `selLoop_ok`) on each.
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## `φ` -/

/-- `phi`: `[aL] := [aPm] [aQm]` (`mulTo_k`). -/
theorem phi_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs phi) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aL] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aL) (I.W + 2) = a * b :=
  mulTo_k h hW (o := aL) (a := aPm) (b := aQm) (by decide) (by decide) (by decide) (by decide) (by decide)
    ha hb ha' hb'

/-! ## Halving -/

theorem halve_shr {X x0 y : Nat} (h : 2 * y + x0 % 2 = X) (hx : X % 2 = x0 % 2) : y = X / 2 := by omega

/-- `halfIf j`: `[j] := x15 ? [j] / 2 : [j]` (`shr_ok` into `aT`, then
`selLoop_ok`); word `W` of `[j]` must be 0 (`shrBody` reads it). -/
theorem halfIf_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    {c : Bool} (h15 : s.gpr .x15 = mask c) (htop : atop I s.mem j = 0) :
    WP isa (seqs (halfIf j)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr j, .arr aT] s.mem t.mem ∧
      av I t.mem j = (if c then av I s.mem j / 2 else av I s.mem j) ∧ atop I t.mem j = 0 ∧
      Keep [.x3, .x4, .x11, .x12, .x14, .x16, .x17] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have sT := h.ws.sl (j := aT) (by decide)
  have sp := slot_sep (w := I.W) hjT
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have hZ := h.hZ
  simp only [halfIf, seqs]
  rw [List.append_assoc]
  -- `[aT] := [j] / 2`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsMov_ok h.ws) fun s₁ ⟨⟨h12, h11, h14, m₁, _⟩, k₁⟩ =>
    WP.mono (base2_ok j aT .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11)
      fun s₂ ⟨⟨h16, h17, m₂, _⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (shr_ok (h.ws.scr.congr k12.wr) h16 h17 ((k₂.gpr .x14 (by decide)).trans h14) hw1
    (by omega) (by omega) (by omega) (by omega)) fun s₃ ⟨hv₃, _, o₃, k₃⟩ => ?_)
  rw [m₂, m₁] at hv₃ o₃
  have f₃ := KF.arr1 (B := I.B) (W := I.W) (j := aT) o₃ (Nat.le_refl _) (by omega)
  have k13 := k12.trans k₃
  have h₃ := h.step f₃ (all_mut_arr (by decide)) k13
  have htop' : word s.mem I.B (slot I.W j + 8 * I.W) = 0 := htop
  rw [htop'] at hv₃
  have hT₃ : av I s₃.mem aT = av I s.mem j / 2 := by
    refine halve_shr (x0 := (word s.mem I.B (slot I.W j)).toNat) (by simpa using hv₃) ?_
    exact (word_mod2 hw1).symm
  have hok : [Rc.arr aT].all Rc.ok = true := by decide
  have hj₃ : av I s₃.mem j = av I s.mem j := f₃.av hok hj (by simp [hjT]) hZ
  have tj₃ : atop I s₃.mem j = 0 := by rw [← htop]; exact f₃.at hok hj (by simp [hjT]) hZ
  -- `[j] := x15 ? [aT] : [j]`.
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsMov_ok h₃.ws) fun s₄ ⟨⟨_, h11₄, h14₄, m₄, _⟩, k₄⟩ =>
    WP.mono (base2_ok aT j .x16 .x17 ((k₄.gpr .x0 (by decide)).trans h₃.ws.x0) h11₄)
      fun s₅ ⟨⟨h16₅, h17₅, m₅, _⟩, k₅⟩ => ?_))
  have k45 := k₄.trans k₅
  refine WP.mono (selLoop_ok (h₃.ws.scr.congr k45.wr) h16₅ h17₅ ((k₅.gpr .x14 (by decide)).trans h14₄)
    ((k13.trans k45).gpr .x15 (by decide) |>.trans h15) hw1 (by omega) (by omega) (by omega) (by omega))
    fun t ⟨hv, o, k₆⟩ => ?_
  rw [m₅, m₄] at hv o
  have f := KF.arr1 (B := I.B) (W := I.W) (j := j) o (Nat.le_refl _) (by omega)
  refine ⟨h₃.step f (all_mut_arr hj) (k45.trans k₆), (f₃.trans f).mono (by simp), ?_, ?_,
    ((k13.trans k45).trans k₆).mono (by decide)⟩
  · dsimp only [av] at hv hT₃ hj₃ ⊢
    rw [hv]
    cases c
    · exact hj₃
    · exact hT₃
  · dsimp only [atop] at tj₃ ⊢; rw [o.word (Or.inr (Nat.le_refl _)) (by omega)]; exact tj₃

/-- The mask of `x` and `y` both even. -/
theorem halve_twoMask (x y : BitVec 64) :
    ((x ||| y) &&& BitVec.setWidth 64 1#16) - BitVec.ofNat 64 1 =
      mask (decide (x.toNat % 2 = 0 ∧ y.toNat % 2 = 0)) := by
  have e : ∀ z : BitVec 64, z &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 (z.toNat % 2) := fun z => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega
  rw [BitVec.and_or_distrib_right, e, e]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> rw [hx, hy] <;> decide

/-- What a step of the halving keeps and changes (x86's, without `sMo`). -/
def TwoP (I : KIn) (s₀ s t : State) : Prop :=
  KS I s₀ t ∧ KF I.B I.W [.arr aU, .arr aV, .arr aL, .arr aT] s.mem t.mem ∧
    atop I t.mem aU = 0 ∧ atop I t.mem aV = 0 ∧ atop I t.mem aL = 0

theorem TwoP.trans {I : KIn} {s₀ s t u : State} (h₁ : TwoP I s₀ s t) (h₂ : TwoP I s₀ t u) : TwoP I s₀ s u :=
  ⟨h₂.1, (h₁.2.1.trans h₂.2.1).mono (by simp), h₂.2.2⟩

/-- The mask of `u` and `v` both even into `x15`. -/
theorem twoMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aU .x16 ++ (base aV .x17 ++ ([ld .x3 .x16, ld .x4 .x17,
      .logic .orr .x .x3 .x3 .x4, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr))))) s
      fun t => (t.mem = s.mem ∧ t.gpr .x15 = mask (decide (av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0))) ∧
        Keep [.x3, .x4, .x11, .x12, .x15, .x16, .x17] s t := by
  have hn := h.ws.scr.nowrap
  have sU := h.ws.sl (j := aU) (by decide)
  have sV := h.ws.sl (j := aV) (by decide)
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h aU) fun s₁ ⟨⟨h16, _, h11, m₁⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aV .x17 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11) fun s₂ ⟨⟨h17, m₂, _⟩, k₂⟩ => ?_
  have hs₂ := h.ws.scr.congr (k₁.trans k₂).wr
  have h16₂ : s₂.gpr .x16 = off I.B (slot I.W aU) := (k₂.gpr .x16 (by decide)).trans h16
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  refine WP.mono (WP.keep [.x3, .x4, .x15] (Q := fun t => t.mem = s.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0))) (by
    brun [h16₂, h17, hs₂.ld (d := slot I.W aU) (by omega), hs₂.ld (d := slot I.W aV) (by omega), hm₂,
      halve_twoMask, word_mod2 (j := aU) hw1, word_mod2 (j := aV) hw1])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨q, k₃⟩ => ⟨q, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- One step: the mask of `u` and `v` both even into `x15`
(`((u | v) & 1) − 1`), the three halvings, and `x6` counted down. -/
theorem twoStep_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hU0 : atop I s.mem aU = 0)
    (hV0 : atop I s.mem aV = 0) (hL0 : atop I s.mem aL = 0) :
    WP isa twoStep s fun t => TwoP I s₀ s t ∧ t.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1 ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) = halveStep (av I s.mem aU, av I s.mem aV, av I s.mem aL) := by
  have hZ := h.hZ
  unfold twoStep
  simp only [List.append_assoc]
  generalize hc : decide (av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0) = c
  refine wp_seqs_append (by simp) (by simp [halfIf]) (WP.mono (twoMask_k h) fun s₁ ⟨⟨m₁, h15₁⟩, k₁⟩ => ?_)
  rw [hc] at h15₁
  have h₁ := h.regs m₁ k₁
  -- `u`.
  refine wp_seqs_append (by simp [halfIf]) (by simp [halfIf]) (WP.mono (halfIf_k h₁ (j := aU) (by decide)
    (by decide) h15₁ (by rw [m₁]; exact hU0)) fun s₂ ⟨h₂, f₂, vU₂, tU₂, k₂⟩ => ?_)
  have hok2 : [Rc.arr aU, Rc.arr aT].all Rc.ok = true := by decide
  have tV₂ : atop I s₂.mem aV = 0 := by rw [← hV0, ← m₁]; exact f₂.at hok2 (by decide) (by decide) hZ
  have tL₂ : atop I s₂.mem aL = 0 := by rw [← hL0, ← m₁]; exact f₂.at hok2 (by decide) (by decide) hZ
  have vV₂ : av I s₂.mem aV = av I s.mem aV := by rw [← m₁]; exact f₂.av hok2 (by decide) (by decide) hZ
  have vL₂ : av I s₂.mem aL = av I s.mem aL := by rw [← m₁]; exact f₂.av hok2 (by decide) (by decide) hZ
  -- `v`.
  refine wp_seqs_append (by simp [halfIf]) (by simp [halfIf]) (WP.mono (halfIf_k h₂ (j := aV) (by decide)
    (by decide) ((k₂.gpr .x15 (by decide)).trans h15₁) tV₂) fun s₃ ⟨h₃, f₃, vV₃, tV₃, k₃⟩ => ?_)
  have hok3 : [Rc.arr aV, Rc.arr aT].all Rc.ok = true := by decide
  have tU₃ : atop I s₃.mem aU = 0 := by rw [← tU₂]; exact f₃.at hok3 (by decide) (by decide) hZ
  have tL₃ : atop I s₃.mem aL = 0 := by rw [← tL₂]; exact f₃.at hok3 (by decide) (by decide) hZ
  have vU₃ : av I s₃.mem aU = av I s₂.mem aU := f₃.av hok3 (by decide) (by decide) hZ
  have vL₃ : av I s₃.mem aL = av I s.mem aL := by rw [← vL₂]; exact f₃.av hok3 (by decide) (by decide) hZ
  -- `φ`.
  refine wp_seqs_append (by simp [halfIf]) (by simp) (WP.mono (halfIf_k h₃ (j := aL) (by decide)
    (by decide) (((k₂.trans k₃).gpr .x15 (by decide)).trans h15₁) tL₃) fun s₄ ⟨h₄, f₄, vL₄, tL₄, k₄⟩ => ?_)
  have hok4 : [Rc.arr aL, Rc.arr aT].all Rc.ok = true := by decide
  have tU₄ : atop I s₄.mem aU = 0 := by rw [← tU₃]; exact f₄.at hok4 (by decide) (by decide) hZ
  have tV₄ : atop I s₄.mem aV = 0 := by rw [← tV₃]; exact f₄.at hok4 (by decide) (by decide) hZ
  have vU₄ : av I s₄.mem aU = av I s₂.mem aU := by rw [← vU₃]; exact f₄.av hok4 (by decide) (by decide) hZ
  have vV₄ : av I s₄.mem aV = av I s₃.mem aV := f₄.av hok4 (by decide) (by decide) hZ
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  simp only [seqs]
  refine WP.mono (dec_ok s₄ .x6) fun t ⟨⟨h6, hm, _⟩, k₅⟩ => ⟨⟨h₄.regs hm k₅,
    by rw [hm, ← m₁]; exact (((f₂.trans f₃).trans f₄)).mono (by simp),
    by rw [hm]; exact tU₄, by rw [hm]; exact tV₄, by rw [hm]; exact tL₄⟩,
    by rw [h6, k14.gpr .x6 (by decide)], ?_⟩
  rw [hm, vU₄, vU₂, vV₄, vV₃, vL₄, vV₂, vL₃, m₁]
  unfold halveStep
  dsimp only
  rw [← hc]
  by_cases hb : av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0
  · simp [hb]
  · simp only [hb, decide_false, Bool.false_eq_true, ite_false]

end VG.Proof.RsaKeyGen.AArch64.Key
