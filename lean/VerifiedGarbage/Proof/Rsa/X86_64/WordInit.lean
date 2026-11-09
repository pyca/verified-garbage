module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordLoop
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Rsa.X86_64.Inv

/-! # Initialization and complete word reduction -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The complete operation also clears the high remainder and writes the reciprocal. -/
def allRanges (W : Nat) : List (Nat × Nat) :=
  [(slot W aR, 8 * (W + 2)), (slot W aT, 8 * (W / 2 + 1)), (slot W aV, 24)]

theorem cover {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (hf : Frm B rs m m')
    (hc : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' := by
  intro x hx
  apply hf x
  intro r hr
  obtain ⟨r', hr', h1, h2⟩ := hc r hr
  have := hx r' hr'
  omega_using [this, h1, h2]

theorem all_mut {W : Nat} {r : Nat × Nat} (hr : r ∈ allRanges W) : Mut r := by
  simp only [allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _

theorem all_bound {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W) (hZ : slot W 17 ≤ Z)
    {r : Nat × Nat} (hr : r ∈ allRanges W) : r.1 + r.2 ≤ Z := by
  simp only [allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.sl (by decide)
  · have := h.sl (j := aT) (by decide); dsimp only; omega_arith
  · exact window_bound h hZ

theorem reciprocal_lt {d : Nat} (hd : 2 ^ 63 ≤ d) : (2 ^ 128 - 1) / d - 2 ^ 64 < 2 ^ 64 := by
  have hq : (2 ^ 128 - 1) / d < 2 ^ 65 := by
    apply (Nat.div_lt_iff_lt_mul (by omega_using [hd])).mpr
    omega_using [hd]
  omega_using [hq]

/-- Setup, reciprocal, public counter and the word loop compute the remainder. -/
theorem code_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 4 ≤ W)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat)
    (hMpos : 0 < wv s.mem B (slot W aM) (W / 2)) :
    WP isa code s fun t =>
      wv t.mem B (slot W aR) (W + 1) =
        wv s.mem B (slot W aD) W % wv s.mem B (slot W aM) (W / 2) ∧
      Frm B (allRanges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hw := h.w2
  have hz := window_bound h hZ
  have hM := h.sl (j := aM) (by decide)
  have hR := h.sl (j := aR) (by decide)
  have hD := h.sl (j := aD) (by decide)
  have sepRM := slot_far (w := W) (i := aR) (j := aM) (by decide)
  have sepRD := slot_far (w := W) (i := aR) (j := aD) (by decide)
  unfold code
  change WP isa (.seq (VG.Impl.Rsa.X86_64.Keys.zeroA aR) (.seq (.block recipSetup)
    (.seq VG.Impl.Bignum.X86_64.R2Words.recip (.seq (.block countSetup) (.loop body .ne))))) s _
  refine WP.seq (WP.mono (zeroA_ok h (by decide)) fun s₁ ⟨z₁, o₁, k₁⟩ => ?_)
  have f₁ : Frm B (allRanges W) s.mem s₁.mem := Frm.of_outside o₁ (by simp [allRanges])
  have h₁ := h.congr f₁ (fun _ hr => all_mut hr) k₁ (by decide)
  have M₁ : wv s₁.mem B (slot W aM) (W / 2) = wv s.mem B (slot W aM) (W / 2) :=
    o₁.wv (by omega_arith) (by omega_arith)
  have top₁ : word s₁.mem B (slot W aM + 8 * (W / 2 - 1)) = word s.mem B (slot W aM + 8 * (W / 2 - 1)) :=
    o₁.word (by omega_arith) (by omega_arith)
  have D₁ : wv s₁.mem B (slot W aD) W = wv s.mem B (slot W aD) W :=
    o₁.wv (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (recipSetup_ok h₁) fun s₂ ⟨h10, h8, h12, m₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (R2w.recip_ok (h₁.scr.congr k₂.2.2) h10 h12 h8
    (by omega_arith) (by omega_arith) (by omega_arith) (by rw [m₂, top₁]; exact hd))
    fun s₃ ⟨m₃, k₃⟩ => ?_)
  have o₃ : Outside B (slot W aV) 8 s₁.mem s₃.mem := by
    rw [m₃, m₂]; exact writeW_outside _ _ _ (by omega_arith)
  have f₃ : Frm B (allRanges W) s₁.mem s₃.mem := by
    apply cover (Frm.of_outside o₃ (by simp : (slot W aV, 8) ∈ [(slot W aV, 8)]))
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, allRanges]
    exact ⟨(slot W aV, 24), by simp, (Nat.le_refl _), by omega_arith⟩
  have k03 := (k₁.trans k₂).trans k₃
  have h₃ := h₁.congr f₃ (fun _ hr => all_mut hr) (k₂.trans k₃) (by decide)
  refine WP.seq (WP.mono (countSetup_ok h₃ hZ) fun s₄ ⟨ha, m₄, k₄⟩ => ?_)
  have o₄ : Outside B (slot W aV + 16) 8 s₃.mem s₄.mem := by
    rw [m₄]; exact writeW_outside _ _ _ (by omega_arith)
  have f₄ : Frm B (allRanges W) s₃.mem s₄.mem := by
    rw [m₄]
    apply cover (range_store (B := B) (W := W) _ (by omega_arith) (by omega_arith) (by omega_arith))
    intro r hr
    simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨(slot W aR, 8 * (W + 2)), by simp [allRanges], (Nat.le_refl _), by omega_arith⟩
    · exact ⟨(slot W aT, 8 * (W / 2 + 1)), by simp [allRanges], (Nat.le_refl _), (Nat.le_refl _)⟩
    · exact ⟨(slot W aV, 24), by simp [allRanges], by omega_arith, by omega_arith⟩
  have h₄ := h₃.congr f₄ (fun _ hr => all_mut hr) k₄ (by decide)
  have eqM : wv s₄.mem B (slot W aM) (W / 2) = wv s.mem B (slot W aM) (W / 2) := by
    rw [o₄.wv (by simp only [slot, aM, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aM, aV]; omega_arith) (by omega_arith), M₁]
  have eqD : wv s₄.mem B (slot W aD) W = wv s.mem B (slot W aD) W := by
    rw [o₄.wv (by simp only [slot, aD, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aD, aV]; omega_arith) (by omega_arith), D₁]
  have eqTop : word s₄.mem B (slot W aM + 8 * (W / 2 - 1)) = word s.mem B (slot W aM + 8 * (W / 2 - 1)) := by
    rw [o₄.word (by simp only [slot, aM, aV]; omega_arith) (by omega_arith),
      o₃.word (by simp only [slot, aM, aV]; omega_arith) (by omega_arith), top₁]
  have z₄ : wv s₄.mem B (slot W aR) (W + 2) = 0 := by
    rw [o₄.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith), z₁]
  have zp := wv_add s₄.mem B (slot W aR) (W / 2) (W + 2 - W / 2)
  rw [show W / 2 + (W + 2 - W / 2) = W + 2 by omega_arith, z₄] at zp
  have zlo : wv s₄.mem B (slot W aR) (W / 2) = 0 := by omega_using [zp]
  have zhi : wv s₄.mem B (slot W aR + 8 * (W / 2)) (W + 2 - W / 2) = 0 := by
    have hp := Nat.two_pow_pos (64 * (W / 2))
    rcases Nat.mul_eq_zero.mp (show 2 ^ (64 * (W / 2)) * wv s₄.mem B (slot W aR + 8 * (W / 2)) (W + 2 - W / 2) = 0 by omega_using [zp]) with he | he
    · omega_using [hp, he]
    · exact he
  refine WP.mono (loop_ok h₄ hZ hW (by rw [m₄, word_writeW_self]) ha (by rw [eqTop]; exact hd)
    (by rw [o₄.word (d := slot W aV) (Or.inl (by omega_arith)) (by omega_arith), m₃, m₂, word_writeW_self,
          BitVec.toNat_ofNat, eqTop];
        rw [Nat.mod_eq_of_lt (reciprocal_lt (by rw [top₁]; exact hd)), top₁])
    zlo (by rw [eqM]; exact hMpos)) fun t ⟨v, fl, kl⟩ => ?_
  have hi : wv t.mem B (slot W aR + 8 * (W / 2)) (W + 1 - W / 2) = 0 := by
    have zh' := wv_eq_zero_iff _ _ _ _ |>.mp zhi
    apply wv_zero
    intro i hi
    rw [fl.word_eq (by
      intro r hr
      simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [slot, aR, aT, aV] <;> omega_arith) (by omega_arith)]
    exact zh' i (by omega_arith)
  refine ⟨?_, ?_, (((k03.trans k₄).trans kl).mono (by decide))⟩
  · have := wv_add t.mem B (slot W aR) (W / 2) (W + 1 - W / 2)
    rw [show W / 2 + (W + 1 - W / 2) = W + 1 by omega_arith, hi, Nat.mul_zero, Nat.add_zero] at this
    rw [this, v, eqD, eqM, Nat.add_zero]
  · apply ((f₁.trans f₃).trans f₄).trans
    apply cover fl
    intro r hr
    simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨(slot W aR, 8 * (W + 2)), by simp [allRanges], (Nat.le_refl _), by omega_arith⟩
    · exact ⟨(slot W aT, 8 * (W / 2 + 1)), by simp [allRanges], (Nat.le_refl _), (Nat.le_refl _)⟩
    · exact ⟨(slot W aV, 24), by simp [allRanges], by omega_arith, by omega_arith⟩

end VG.Proof.Rsa.X86_64.WordDivide
