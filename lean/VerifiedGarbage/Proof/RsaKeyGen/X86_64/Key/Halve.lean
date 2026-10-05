import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Front
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows

/-!
# An RSA key from its primes on x86-64: `φ` and the halving

`φ = (p − 1)(q − 1)` (`phi_k`), and the `64 W` steps that halve `u`, `v` and
`φ` while `u` and `v` are both even (`twos_k`, `halveIter`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-! ## `φ` -/

theorem ofNat_shr1 {W : Nat} (hW : W < 2 ^ 64) : BitVec.ofNat 64 W >>> 1 = BitVec.ofNat 64 (W / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem ofNat_sub' {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega)]
  omega

/-- `phi`: `[aL] := [aPm] [aQm]`, `w` words each, for `W = 2 w`. -/
theorem phi_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs phi) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aL] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aL) (I.W + 2) = a * b := by
  have hn := h.ws.scr.nowrap
  have sP := h.ws.sl (j := aPm) (by decide)
  have sQ := h.ws.sl (j := aQm) (by decide)
  have sL := h.ws.sl (j := aL) (by decide)
  have p1 := slot_far (w := I.W) (i := aPm) (j := aL) (by decide)
  have p2 := slot_far (w := I.W) (i := aQm) (j := aL) (by decide)
  have hw2 := h.ws.w2
  have hw1 := h.ws.w1
  simp only [phi, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aL) (by decide)) fun s₁ ⟨h₁, f₁, z₁, _⟩ => ?_)
  have hok : [Rc.arr aL].all Rc.ok = true := by decide
  have va : wv s₁.mem I.B (slot I.W aPm) w = a := by
    rw [f₁.wv hok (j := aPm) (by decide) (by decide) (Nat.le_refl _) (by omega) h.hZ, ← ha]
    dsimp only [av] at ha
    exact wv_low_of_lt (by omega) (by rw [ha]; exact ha')
  have vb : wv s₁.mem I.B (slot I.W aQm) w = b := by
    rw [f₁.wv hok (j := aQm) (by decide) (by decide) (Nat.le_refl _) (by omega) h.hZ, ← hb]
    dsimp only [av] at hb
    exact wv_low_of_lt (by omega) (by rw [hb]; exact hb')
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h₁.ws.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ => ?_))
  have hdi₂ : s₂.gpr .rdi = I.B := (k₂.gpr (by decide)).trans h₁.ws.rdi
  refine WP.block_append_iff.mpr (WP.mono (base_ok aPm (r := .r11) (by decide) hdi₂ h9) fun s₃ ⟨h11, m₃, k₃⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aQm (r := .rax) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
    ((k₃.gpr (by decide)).trans h9)) fun s₄ ⟨hax, m₄, k₄⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aL (r := .r8) (by decide)
    (((k₃.trans k₄).gpr (by decide)).trans hdi₂) (((k₃.trans k₄).gpr (by decide)).trans h9))
    fun s₅ ⟨h8, m₅, k₅⟩ => ?_)
  have h12₅ : s₅.gpr .r12 = BitVec.ofNat 64 I.W := (((k₃.trans k₄).trans k₅).gpr (by decide)).trans h12
  have hax₅ : s₅.gpr .rax = off I.B (slot I.W aQm) := (k₅.gpr (by decide)).trans hax
  refine WP.mono (WP.keep [.r9, .r10, .r12] (Q := fun t => t.gpr .r9 = off I.B (slot I.W aQm) ∧
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s₅.mem) (by
    xrun [h12₅, hax₅, ofNat_shr1 (show I.W < 2 ^ 64 by omega)]
    refine ⟨by rw [hW]; congr 1; omega, ?_⟩
    rw [ofNat_sub' (by omega) (by omega)]; congr 1; omega) rfl) fun s₆ ⟨⟨h9₆, h10₆, h12₆, m₆⟩, k₆⟩ => ?_
  have k26 := (((k₂.trans k₃).trans k₄).trans k₅).trans k₆
  have hm₆ : s₆.mem = s₁.mem := by rw [m₆, m₅, m₄, m₃, m₂]
  have hz₆ : wv s₆.mem I.B (slot I.W aL) (w + w + 2) = 0 := by rw [hm₆, ← z₁]; congr 1; omega
  refine WP.mono (mulRows_ok (h₁.ws.scr.congr k26.2.2) ((k₄.trans k₅ |>.trans k₆).gpr (by decide) |>.trans h11)
    h9₆ h10₆ h12₆ ((k₆.gpr (by decide)).trans h8) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by rw [hz₆]; exact Nat.two_pow_pos _)) fun t ⟨hv, o, k₇⟩ => ?_
  rw [hz₆, hm₆, va, vb, Nat.zero_add] at hv
  rw [hm₆] at o
  have f := KF.arr1 (I := I) (j := aL) o (Nat.le_refl _) (by omega)
  refine ⟨h₁.step f (all_mut_arr (by decide)) (k26.trans k₇) (by decide), (f₁.trans f).mono (by simp), ?_⟩
  rw [show I.W + 2 = w + w + 2 by omega]; exact hv

/-! ## Halving -/

theorem shr_half {X x0 y : Nat} (h : y * 2 + x0 % 2 = X) (hx : X % 2 = x0 % 2) : y = X / 2 := by omega

/-- `halfIf j`: `[j] := [j] / 2` if `sMo` is the mask of `c`, for word `W`
of `[j]` zero. -/
theorem halfIf_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    {c : Bool} (hmo : word s.mem I.B (8 * sMo) = mask c) (htop : atop I s.mem j = 0) :
    WP isa (seqs (halfIf j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j, .arr aT] s.mem t.mem ∧
      av I t.mem j = (if c then av I s.mem j / 2 else av I s.mem j) ∧ atop I t.mem j = 0 ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14, .rbp] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have sT := h.ws.sl (j := aT) (by decide)
  have sp := slot_far (w := I.W) hjT
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have hZ := h.hZ
  simp only [halfIf, seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok j aT (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.ws.rdi) h9 (by decide)) fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.seq (WP.mono (shr_ok (h.ws.scr.congr (k₁.trans k₂).2.2) hsi h8 ((k₂.gpr (by decide)).trans h12) hw1
    (by omega) (by omega) (by omega) (by omega)) fun s₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  rw [m₂, m₁] at hv₃ o₃
  have f₃ := KF.arr1 (I := I) (j := aT) o₃ (Nat.le_refl _) (by omega)
  have h₃ := h.step f₃ (all_mut_arr (by decide)) ((k₁.trans k₂).trans k₃) (by decide)
  have htop' : word s.mem I.B (slot I.W j + 8 * I.W) = 0 := htop
  rw [htop'] at hv₃
  have hT₃ : av I s₃.mem aT = av I s.mem j / 2 := by
    refine shr_half (x0 := (word s.mem I.B (slot I.W j)).toNat) (by simpa using hv₃) ?_
    rw [← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
  have hok : [Rc.arr aT].all Rc.ok = true := by decide
  have hj₃ : av I s₃.mem j = av I s.mem j := f₃.arr hok hj (by simp [hjT]) hZ
  have tj₃ : atop I s₃.mem j = 0 := by rw [← htop]; exact f₃.top hok hj (by simp [hjT]) hZ
  have hmo₃ : word s₃.mem I.B (8 * sMo) = mask c := by rw [f₃.word hok (by decide) (by decide), hmo]
  have k13 := (k₁.trans k₂).trans k₃
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!c) ∧
      t.mem = s₃.mem) (by
    have hl := h₃.ws.scr.ld (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega)
    xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hl, hmo₃, sxM1, maskNot]) rfl) fun s₄ ⟨⟨hbp, m₄⟩, k₄⟩ =>
    WP.mono (base2_ok j aT (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₄.gpr (by decide)).trans h₃.ws.rdi) ((k₄.gpr (by decide)).trans (((k₂.trans k₃).gpr (by decide)).trans h9))
      (by decide)) fun s₅ ⟨h8₅, hsi₅, m₅, k₅⟩ => ?_))
  refine WP.mono (sel_ok (h.ws.scr.congr ((k13.trans k₄).trans k₅).2.2) h8₅ hsi₅ ((k₅.gpr (by decide)).trans hbp)
    (((k₄.trans k₅).gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))) (by omega)
    (by omega) (by omega) (by omega) (by omega)) fun t ⟨hv, o, k₆⟩ => ?_
  rw [m₅, m₄] at hv o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega)
  refine ⟨h₃.step f (all_mut_arr hj) ((k₄.trans k₅).trans k₆) (by decide), (f₃.trans f).mono (by simp), ?_, ?_,
    (((k13.trans k₄).trans k₅).trans k₆).mono (by simp)⟩
  · dsimp only [av] at hv ⊢; rw [hv]
    cases c <;> simp only [Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true]
    · exact hj₃
    · exact hT₃
  · dsimp only [atop]; rw [o.word (Or.inr (Nat.le_refl _)) (by omega)]; exact tj₃

theorem and1_ofNat (x : BitVec 64) : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  omega

/-- The mask of `x` and `y` both even. -/
theorem twoMask (x y : BitVec 64) :
    ((x ||| y) &&& 1) - 1 = mask (decide (x.toNat % 2 = 0 ∧ y.toNat % 2 = 0)) := by
  rw [BitVec.and_or_distrib_right, and1_ofNat, and1_ofNat]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> rw [hx, hy] <;> decide

/-- `add r13, 1; cmp r13, r11`. -/
theorem countP_ok (s : State) {j N : Nat} (hj : s.gpr .r13 = BitVec.ofNat 64 j)
    (hN : s.gpr .r11 = BitVec.ofNat 64 N) (hjN : j + 1 < 2 ^ 64) (hN' : N < 2 ^ 64) :
    WP isa (.block countP) s fun s' =>
      s'.zf = some (decide (j + 1 = N)) ∧ s'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧
      s'.mem = s.mem ∧ Keep [.r13] s s' := by
  refine WP.mono (WP.keep [.r13] (Q := fun s' => s'.zf = some (decide (j + 1 = N)) ∧
    s'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧ s'.mem = s.mem) ?_ rfl) fun s' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold countP
  xrun [hj, hN, ofNat_add_one, ofNat_sub_beq hjN hN']

/-- What a step of the halving keeps and changes. -/
def TwoP (I : KIn) (m₀ : Mem) (s t : State) : Prop :=
  KS I m₀ t ∧ KF I.B I.W [.arr aU, .arr aV, .arr aL, .arr aT, .hdr sMo] s.mem t.mem ∧
    atop I t.mem aU = 0 ∧ atop I t.mem aV = 0 ∧ atop I t.mem aL = 0

/-- One step of the halving, and the count. -/
theorem twoStep_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hU0 : atop I s.mem aU = 0)
    (hV0 : atop I s.mem aV = 0) (hL0 : atop I s.mem aL = 0) {j : Nat} (h13 : s.gpr .r13 = BitVec.ofNat 64 j)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (64 * I.W)) (hj : j < 64 * I.W) :
    WP isa twoStep s fun t => t.zf = some (decide (j + 1 = 64 * I.W)) ∧ t.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧
      t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧ TwoP I m₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) = halveStep (av I s.mem aU, av I s.mem aV, av I s.mem aL) := by
  have hn := h.ws.scr.nowrap
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have hZ := h.hZ
  have sU := h.ws.sl (j := aU) (by decide)
  have sV := h.ws.sl (j := aV) (by decide)
  unfold twoStep
  simp only [List.append_assoc]
  -- The mask of both even into `sMo`.
  generalize hc : decide (av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0) = c
  have hb : WP isa (.block (ws ++ base aU .rbx ++ base aV .r10 ++ [.mov .rax (.mem (at0 .rbx)),
      .alu .or .rax (.mem (at0 .r10)), .alu .and .rax (.imm 1), .alu .sub .rax (.imm 1), .store (hdr sMo) .rax])) s
      fun t => t.mem = s.mem.writeW (off I.B (8 * sMo)) (mask c) ∧ Keep [.r12, .r9, .rbx, .r10, .rax] s t := by
    rw [List.append_assoc, List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_)
    have hdi₁ : s₁.gpr .rdi = I.B := (k₁.gpr (by decide)).trans h.ws.rdi
    refine WP.mono (base_ok aU (r := .rbx) (by decide) hdi₁ h9) fun s₂ ⟨hbx, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aV (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
      ((k₂.gpr (by decide)).trans h9)) fun s₃ ⟨h10, m₃, k₃⟩ => ?_
    have hs₃ := h.ws.scr.congr ((k₁.trans k₂).trans k₃).2.2
    have hbx₃ : s₃.gpr .rbx = off I.B (slot I.W aU) := (k₃.gpr (by decide)).trans hbx
    have hdi₃ : s₃.gpr .rdi = I.B := ((k₂.trans k₃).gpr (by decide)).trans hdi₁
    have hm₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
    have eU : (s.mem.readW (off I.B (slot I.W aU)) 64).toNat % 2 = av I s.mem aU % 2 := by
      rw [← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
    have eV : (s.mem.readW (off I.B (slot I.W aV)) 64).toNat % 2 = av I s.mem aV % 2 := by
      rw [← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
    have hmask : ((s.mem.readW (off I.B (slot I.W aU)) 64 ||| s.mem.readW (off I.B (slot I.W aV)) 64) &&& 1) -
        1 = mask c := by
      rw [twoMask, eU, eV, hc]
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * sMo)) (mask c)) (by
      xrun [State.ea, at0, hdr, hbx₃, h10, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₃.ld (d := slot I.W aU) (by omega), hs₃.ld (d := slot I.W aV) (by omega),
        hs₃.st (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega), hm₃, hmask]) rfl)
      fun t ⟨hm, k₄⟩ => ⟨hm, (((k₁.trans k₂).trans k₃).trans k₄).mono (by simp)⟩
  refine wp_seqs_append (by simp) (by simp [halfIf]) (WP.mono hb fun s₁ ⟨hm₁, k₁⟩ => ?_)
  obtain ⟨h₁, f₁, hmo₁⟩ := h.hdrW (i := sMo) (by unfold sMo sFn; omega) hm₁ k₁ (by decide)
  have hok1 : [Rc.hdr sMo].all Rc.ok = true := by decide
  have tU₁ : atop I s₁.mem aU = 0 := by rw [← hU0]; exact f₁.top hok1 (by decide) (by decide) hZ
  have tV₁ : atop I s₁.mem aV = 0 := by rw [← hV0]; exact f₁.top hok1 (by decide) (by decide) hZ
  have tL₁ : atop I s₁.mem aL = 0 := by rw [← hL0]; exact f₁.top hok1 (by decide) (by decide) hZ
  have vU₁ : av I s₁.mem aU = av I s.mem aU := f₁.arr hok1 (by decide) (by decide) hZ
  have vV₁ : av I s₁.mem aV = av I s.mem aV := f₁.arr hok1 (by decide) (by decide) hZ
  have vL₁ : av I s₁.mem aL = av I s.mem aL := f₁.arr hok1 (by decide) (by decide) hZ
  -- `u`.
  refine wp_seqs_append (by simp [halfIf]) (by simp [halfIf]) (WP.mono (halfIf_k h₁ (j := aU) (by decide)
    (by decide) hmo₁ tU₁) fun s₂ ⟨h₂, f₂, vU₂, tU₂, k₂⟩ => ?_)
  have hok2 : [Rc.arr aU, Rc.arr aT].all Rc.ok = true := by decide
  have hmo₂ : word s₂.mem I.B (8 * sMo) = mask c := by rw [f₂.word hok2 (by decide) (by decide), hmo₁]
  have tV₂ : atop I s₂.mem aV = 0 := by rw [← tV₁]; exact f₂.top hok2 (by decide) (by decide) hZ
  have tL₂ : atop I s₂.mem aL = 0 := by rw [← tL₁]; exact f₂.top hok2 (by decide) (by decide) hZ
  have vV₂ : av I s₂.mem aV = av I s.mem aV := by rw [← vV₁]; exact f₂.arr hok2 (by decide) (by decide) hZ
  have vL₂ : av I s₂.mem aL = av I s.mem aL := by rw [← vL₁]; exact f₂.arr hok2 (by decide) (by decide) hZ
  -- `v`.
  refine wp_seqs_append (by simp [halfIf]) (by simp [halfIf]) (WP.mono (halfIf_k h₂ (j := aV) (by decide)
    (by decide) hmo₂ tV₂) fun s₃ ⟨h₃, f₃, vV₃, tV₃, k₃⟩ => ?_)
  have hok3 : [Rc.arr aV, Rc.arr aT].all Rc.ok = true := by decide
  have hmo₃ : word s₃.mem I.B (8 * sMo) = mask c := by rw [f₃.word hok3 (by decide) (by decide), hmo₂]
  have tU₃ : atop I s₃.mem aU = 0 := by rw [← tU₂]; exact f₃.top hok3 (by decide) (by decide) hZ
  have tL₃ : atop I s₃.mem aL = 0 := by rw [← tL₂]; exact f₃.top hok3 (by decide) (by decide) hZ
  have vU₃ : av I s₃.mem aU = av I s₂.mem aU := f₃.arr hok3 (by decide) (by decide) hZ
  have vL₃ : av I s₃.mem aL = av I s.mem aL := by rw [← vL₂]; exact f₃.arr hok3 (by decide) (by decide) hZ
  -- `φ`.
  refine wp_seqs_append (by simp [halfIf]) (by simp) (WP.mono (halfIf_k h₃ (j := aL) (by decide)
    (by decide) hmo₃ tL₃) fun s₄ ⟨h₄, f₄, vL₄, tL₄, k₄⟩ => ?_)
  have hok4 : [Rc.arr aL, Rc.arr aT].all Rc.ok = true := by decide
  have tU₄ : atop I s₄.mem aU = 0 := by rw [← tU₃]; exact f₄.top hok4 (by decide) (by decide) hZ
  have tV₄ : atop I s₄.mem aV = 0 := by rw [← tV₃]; exact f₄.top hok4 (by decide) (by decide) hZ
  have vU₄ : av I s₄.mem aU = av I s₂.mem aU := by rw [← vU₃]; exact f₄.arr hok4 (by decide) (by decide) hZ
  have vV₄ : av I s₄.mem aV = av I s₃.mem aV := f₄.arr hok4 (by decide) (by decide) hZ
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  simp only [seqs]
  refine WP.mono (countP_ok s₄ ((k14.gpr (by decide)).trans h13) ((k14.gpr (by decide)).trans h11) (by omega)
    (by omega)) fun t ⟨hz, h13', hm, k₅⟩ => ⟨hz, h13', (k₅.gpr (by decide)).trans ((k14.gpr (by decide)).trans h11),
      ⟨h₄.step (cs := []) (by rw [hm]; exact KF.refl _ _ _) rfl k₅ (by decide),
        by rw [hm]; exact ((((f₁.trans f₂).trans f₃).trans f₄)).mono (by simp),
        by rw [hm]; exact tU₄, by rw [hm]; exact tV₄, by rw [hm]; exact tL₄⟩, ?_⟩
  rw [hm, vU₄, vU₂, vV₄, vV₃, vL₄, vU₁, vV₂, vL₃]
  unfold halveStep
  dsimp only
  rw [← hc]
  by_cases hb : av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0
  · simp [hb]
  · simp only [hb, decide_false, Bool.false_eq_true, ite_false]

end VG.Proof.RsaKeyGen.X86_64.Key
