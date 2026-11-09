module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordSetup
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFrame
import VerifiedGarbage.Proof.Rsa.X86_64.WordStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv

/-! # Iterating normalized remainders over the private exponent -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The high input inputPrefix after processing the words above `j`. -/
def inputPrefix (m : Mem) (B : Addr) (W j : Nat) : Nat :=
  wv m B (slot W aD + 8 * j) (W - j)

theorem prefix_step (m : Mem) (B : Addr) {W j : Nat} (hj : 1 ≤ j) (hjW : j ≤ W) :
    inputPrefix m B W (j - 1) = (word m B (slot W aD + 8 * (j - 1))).toNat +
      2 ^ 64 * inputPrefix m B W j := by
  unfold inputPrefix
  rw [show W - (j - 1) = 1 + (W - j) by omega_using [hj, hjW], wv_add]
  simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul]
  rw [show slot W aD + 8 * (j - 1) + 8 * 1 = slot W aD + 8 * j by omega_using [hj]]

theorem core_ok {s : State} {B : Addr} {Z W j : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 4 ≤ W) (hj : 1 ≤ j) (hjW : j ≤ W)
    (hc : word s.mem B (slot W aV + 16) = BitVec.ofNat 64 j)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat)
    (hv : (word s.mem B (slot W aV)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat - 2 ^ 64)
    (hx : wv s.mem B (slot W aR) (W / 2) < wv s.mem B (slot W aM) (W / 2)) :
    WP isa (.seq (.block stepSetup) Impl.Rsa.X86_64.WordReduce.step) s fun t =>
      wv t.mem B (slot W aR) (W / 2) =
        (wv s.mem B (slot W aR) (W / 2) * 2 ^ 64 +
          (word s.mem B (slot W aD + 8 * (j - 1))).toNat) % wv s.mem B (slot W aM) (W / 2) ∧
      word t.mem B (slot W aV + 16) = BitVec.ofNat 64 j ∧
      Frm B (ranges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := window_bound h hZ
  have hn := h.scr.nowrap
  have hw := h.w2
  have hM := h.sl (j := aM) (by decide)
  have hR := h.sl (j := aR) (by decide)
  have hT := h.sl (j := aT) (by decide)
  have hsep : slot W aT + 8 * (W / 2 + 1) ≤ slot W aR ∨
      slot W aR + 8 * (W / 2) ≤ slot W aT := by
    simp only [slot, aT, aR]; omega_arith
  have hsepM : slot W aT + 8 * (W / 2 + 1) ≤ slot W aM ∨
      slot W aM + 8 * (W / 2) ≤ slot W aT := by
    simp only [slot, aT, aM]; omega_arith
  refine WP.seq (WP.mono (stepSetup_ok h hZ hj hjW hc) fun s₁ ⟨hbx, h10, h8, hbp, h12, hm₁, k₁⟩ => ?_)
  have f₁ : Frm B (ranges W) s.mem s₁.mem := by rw [hm₁]; exact range_store _ (by omega_arith) (by omega_arith) (by omega_arith)
  have h₁ := range_ws h f₁ k₁
  have M₁ := range_modulus f₁ (by omega_arith)
  have top₁ := range_top hW f₁ (by omega_arith)
  have recip₁ := range_recip f₁ (by omega_arith)
  have X₁ : wv s₁.mem B (slot W aR) (W / 2) = wv s.mem B (slot W aR) (W / 2) := by
    rw [hm₁]
    apply (writeW_outside s.mem B _ (by omega_arith)).wv _ (by omega_arith)
    left; simp only [slot, aR, aV]; omega_arith
  refine WP.mono (WordReduce.step_ok h₁.scr hbx h10 h8 h12 hbp
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) hsep hsepM (by rw [top₁]; exact hd) (by rw [recip₁, top₁]; exact hv)
    (by rw [X₁, M₁]; exact hx)) fun s₂ ⟨v₂, f₂, k₂⟩ => ?_
  have f₂' := range_core f₂
  have f02 := f₁.trans f₂'
  have k02 := k₁.trans k₂
  have h₂ := range_ws h f02 (k02.mono (by simp))
  have c₂ : word s₂.mem B (slot W aV + 16) = BitVec.ofNat 64 j := by
    rw [f₂.word_eq (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [slot, aT, aR, aV] <;> omega_arith) (by omega_arith)]
    rw [hm₁]
    rw [(writeW_outside s.mem B _ (by omega_arith)).word (Or.inr (by omega_arith)) (by omega_arith), hc]
  exact ⟨by rw [v₂, X₁, M₁, hm₁, word_writeW_self], c₂, f02, k02.mono (by simp)⟩

theorem body_ok {s : State} {B : Addr} {Z W j : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 4 ≤ W) (hj : 1 ≤ j) (hjW : j ≤ W)
    (hc : word s.mem B (slot W aV + 16) = BitVec.ofNat 64 j)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat)
    (hv : (word s.mem B (slot W aV)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat - 2 ^ 64)
    (hx : wv s.mem B (slot W aR) (W / 2) < wv s.mem B (slot W aM) (W / 2)) :
    WP isa body s fun t =>
      wv t.mem B (slot W aR) (W / 2) =
        (wv s.mem B (slot W aR) (W / 2) * 2 ^ 64 +
          (word s.mem B (slot W aD + 8 * (j - 1))).toNat) % wv s.mem B (slot W aM) (W / 2) ∧
      word t.mem B (slot W aV + 16) = BitVec.ofNat 64 (j - 1) ∧
      t.gpr .rax = BitVec.ofNat 64 (j - 1) ∧ t.zf = some (decide (j = 1)) ∧
      Frm B (ranges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := window_bound h hZ
  have hn := h.scr.nowrap
  have hw := h.w2
  have hM := h.sl (j := aM) (by decide)
  have hR := h.sl (j := aR) (by decide)
  have hT := h.sl (j := aT) (by decide)
  have hsep : slot W aT + 8 * (W / 2 + 1) ≤ slot W aR ∨
      slot W aR + 8 * (W / 2) ≤ slot W aT := by
    simp only [slot, aT, aR]; omega_arith
  have hsepM : slot W aT + 8 * (W / 2 + 1) ≤ slot W aM ∨
      slot W aM + 8 * (W / 2) ≤ slot W aT := by
    simp only [slot, aT, aM]; omega_arith
  unfold body
  change WP isa (.seq (.block stepSetup) (.seq Impl.Rsa.X86_64.WordReduce.step (.block next))) s _
  refine WP.seq (WP.mono (stepSetup_ok h hZ hj hjW hc) fun s₁ ⟨hbx, h10, h8, hbp, h12, hm₁, k₁⟩ => ?_)
  have f₁ : Frm B (ranges W) s.mem s₁.mem := by rw [hm₁]; exact range_store _ (by omega_arith) (by omega_arith) (by omega_arith)
  have h₁ := range_ws h f₁ k₁
  have M₁ := range_modulus f₁ (by omega_arith)
  have top₁ := range_top hW f₁ (by omega_arith)
  have recip₁ := range_recip f₁ (by omega_arith)
  have X₁ : wv s₁.mem B (slot W aR) (W / 2) = wv s.mem B (slot W aR) (W / 2) := by
    rw [hm₁]
    apply (writeW_outside s.mem B _ (by omega_arith)).wv _ (by omega_arith)
    left; simp only [slot, aR, aV]; omega_arith
  refine WP.seq (WP.mono (WordReduce.step_ok h₁.scr hbx h10 h8 h12 hbp
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) hsep hsepM (by rw [top₁]; exact hd) (by rw [recip₁, top₁]; exact hv)
    (by rw [X₁, M₁]; exact hx)) fun s₂ ⟨v₂, f₂, k₂⟩ => ?_)
  have f₂' := range_core f₂
  have f02 := f₁.trans f₂'
  have k02 := k₁.trans k₂
  have h₂ := range_ws h f02 (k02.mono (by simp))
  have c₂ : word s₂.mem B (slot W aV + 16) = BitVec.ofNat 64 j := by
    rw [f₂.word_eq (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [slot, aT, aR, aV] <;> omega_arith) (by omega_arith)]
    rw [hm₁]
    rw [(writeW_outside s.mem B _ (by omega_arith)).word (Or.inr (by omega_arith)) (by omega_arith), hc]
  refine WP.mono (next_ok h₂ hZ hj hjW c₂) fun t ⟨ha, hz', hm₃, k₃⟩ => ?_
  have f₃ : Frm B (ranges W) s₂.mem t.mem := by rw [hm₃]; exact range_store _ (by omega_arith) (by omega_arith) (by omega_arith)
  have X₃ : wv t.mem B (slot W aR) (W / 2) = wv s₂.mem B (slot W aR) (W / 2) := by
    rw [hm₃]
    apply (writeW_outside s₂.mem B _ (by omega_arith)).wv _ (by omega_arith)
    left; simp only [slot, aR, aV]; omega_arith
  refine ⟨?_, ?_, ha, hz', f02.trans f₃, (k02.trans k₃).mono (by simp)⟩
  · rw [X₃, v₂, X₁, M₁, hm₁, word_writeW_self]
  · rw [hm₃, word_writeW_self]

/-- The fixed word-count loop computes the entire dividend's remainder. -/
theorem loop_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 4 ≤ W)
    (hc : word s.mem B (slot W aV + 16) = BitVec.ofNat 64 W)
    (ha : s.gpr .rax = BitVec.ofNat 64 W)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat)
    (hv : (word s.mem B (slot W aV)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat - 2 ^ 64)
    (h0 : wv s.mem B (slot W aR) (W / 2) = 0)
    (hMpos : 0 < wv s.mem B (slot W aM) (W / 2)) :
    WP isa (.loop body .ne) s fun t =>
      wv t.mem B (slot W aR) (W / 2) =
        wv s.mem B (slot W aD) W % wv s.mem B (slot W aM) (W / 2) ∧
      Frm B (ranges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hw := h.w2
  have hz := window_bound h hZ
  have hMz := h.sl (j := aM) (by decide)
  have hDz := h.sl (j := aD) (by decide)
  let M := wv s.mem B (slot W aM) (W / 2)
  let Inv (i : Nat) (t : State) : Prop :=
    Ws t B Z W ∧ word t.mem B (slot W aV + 16) = BitVec.ofNat 64 (W - i) ∧
      wv t.mem B (slot W aR) (W / 2) = inputPrefix s.mem B W (W - i) % M ∧
      Frm B (ranges W) s.mem t.mem ∧ Keep mmRegs s t
  refine wp_countdown (cnt := .rax) (by omega_using [hw]) (by omega_using [hW]) Inv ?_ ?_ ?_ ha
  · intro i hi t hI hcnt
    obtain ⟨ht, ct, xt, ft, kt⟩ := hI
    have tm := range_modulus ft (by omega_arith)
    have tt := range_top hW ft (by omega_arith)
    have tv := range_recip ft (by omega_arith)
    refine WP.mono (body_ok ht hZ hW (by omega_using [hi]) (by omega_arith) ct
      (by rw [tt]; exact hd) (by rw [tv, tt]; exact hv)
      (by rw [xt, tm]; exact Nat.mod_lt _ hMpos)) fun t' ⟨xt', ct', at', zt', ft', kt'⟩ => ?_
    have ff := ft.trans ft'
    have kk : Keep mmRegs s t' := (kt.trans kt').mono (by simp)
    have nextI : Inv (i + 1) t' := by
      refine ⟨range_ws h ff kk, ?_, ?_, ff, kk⟩
      · simpa only [Nat.sub_add_eq] using ct'
      · rw [xt', xt, tm]
        have digit : word t.mem B (slot W aD + 8 * (W - i - 1)) =
            word s.mem B (slot W aD + 8 * (W - i - 1)) :=
          ft.word_eq (by
            intro r hr
            simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> simp only [slot, aD, aR, aT, aV] <;> omega_arith)
            (by omega_arith)
        rw [digit, show W - (i + 1) = W - i - 1 by omega_arith,
          prefix_step s.mem B (by omega_using [hi]) (by omega_arith)]
        simp only [M, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.add_comm, Nat.mul_comm]
    refine ⟨nextI, ?_, ?_⟩
    · rw [at', show t.gpr .rax = BitVec.ofNat 64 (W - i) from hcnt,
        ofNat64_pred (by omega_using [hi]) (by omega_using [hw])]
    · rw [zt', show t.gpr .rax = BitVec.ofNat 64 (W - i) from hcnt,
        ofNat64_pred (by omega_using [hi]) (by omega_using [hw]),
        ofNat64_beq_zero (by omega_using [hw])]
      simp only [show (W - i - 1 = 0) ↔ W - i = 1 by omega_using [hi]]
  · intro t hI
    obtain ⟨_, _, xt, ft, kt⟩ := hI
    exact ⟨by simpa only [Nat.sub_self, inputPrefix, Nat.mul_zero, Nat.add_zero, Nat.sub_zero] using xt, ft, kt⟩
  · exact ⟨h, by simpa using hc, by simp only [Nat.sub_zero, inputPrefix, Nat.sub_self, wv, Nat.zero_mod, h0],
      Frm.refl _ _ _, Keep.refl _ _⟩

end VG.Proof.Rsa.X86_64.WordDivide
