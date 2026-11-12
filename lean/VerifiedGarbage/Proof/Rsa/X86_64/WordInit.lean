module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordLoop
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
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

/-- The dividend's words from `j` on, for a dividend below `2^(64 X)`, `X = j + (W / 2 - 1)`: its
`W / 2 - 1` words from `j`. -/
theorem seeded_prefix (m : Mem) (B : Addr) {d W j X : Nat} (hjX : j + (W / 2 - 1) = X) (hX : X ≤ W)
    (hlt : wv m B d W < 2 ^ (64 * X)) :
    wv m B (d + 8 * j) (W - j) = wv m B (d + 8 * j) (W / 2 - 1) ∧
      wv m B (d + 8 * j) (W / 2 - 1) < 2 ^ (64 * (W / 2 - 1)) := by
  have e := wv_add m B d j (W - j)
  rw [show j + (W - j) = W by omega_arith] at e
  have hP : wv m B (d + 8 * j) (W - j) < 2 ^ (64 * (W / 2 - 1)) := by
    have hp : 2 ^ (64 * X) = 2 ^ (64 * j) * 2 ^ (64 * (W / 2 - 1)) := by
      rw [← Nat.pow_add, ← hjX, Nat.mul_add]
    have : 2 ^ (64 * j) * wv m B (d + 8 * j) (W - j) < 2 ^ (64 * j) * 2 ^ (64 * (W / 2 - 1)) := by
      rw [← hp]; omega_arith
    exact Nat.lt_of_mul_lt_mul_left this
  have low := wv_low_of_lt (m := m) (B := B) (e := d + 8 * j) (v := W / 2 - 1) (w := W - j) (by omega_arith) hP
  exact ⟨low.symm, low ▸ hP⟩

/-- Setup, seed, reciprocal, public counter and the word loop compute the remainder, for a
dividend of `xw W top` words. -/
theorem code_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 6 ≤ W) {top : Option Nat} (hk : ∀ k, top = some k → k ≤ W / 2)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat)
    (hMpos : 0 < wv s.mem B (slot W aM) (W / 2)) :
    WP isa (code top) s fun t =>
      (wv s.mem B (slot W aD) W < 2 ^ (64 * xw W top) → wv t.mem B (slot W aR) (W + 1) =
        wv s.mem B (slot W aD) W % wv s.mem B (slot W aM) (W / 2)) ∧
      Frm B (allRanges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hw := h.w2
  have hz := window_bound h hZ
  have hM := h.sl (j := aM) (by decide)
  have hR := h.sl (j := aR) (by decide)
  have hD := h.sl (j := aD) (by decide)
  have sepRM := slot_far (w := W) (i := aR) (j := aM) (by decide)
  have sepRD := slot_far (w := W) (i := aR) (j := aD) (by decide)
  have hj := j0_add top (W := W) (by omega_arith)
  have hxw : xw W top ≤ W := by
    cases top with
    | none => simp only [xw]; omega_arith
    | some k => have := hk k rfl; simp only [xw]; omega_arith
  have hj1 : 1 ≤ j0 W top := by cases top <;> simp only [j0] <;> omega_arith
  unfold code
  change WP isa (.seq (VG.Impl.Rsa.X86_64.Keys.zeroA aR) (.seq (seed top) (.seq (.block recipSetup)
    (.seq VG.Impl.Bignum.X86_64.R2Words.recip (.seq (.block (countSetup top)) (.loop body .ne)))))) s _
  refine WP.seq (WP.mono (zeroA_ok h (by decide)) fun s₀ ⟨z₀, o₀, k₀⟩ => ?_)
  have f₀ : Frm B (allRanges W) s.mem s₀.mem := Frm.of_outside o₀ (by simp [allRanges])
  have h₀ := h.congr f₀ (fun _ hr => all_mut hr) k₀ (by decide)
  refine WP.seq (WP.mono (seed_ok h₀ hW hk) fun s₁ ⟨v₁, oS, kS⟩ => ?_)
  have o₁ : Outside B (slot W aR) (8 * (W + 2)) s.mem s₁.mem :=
    o₀.trans (oS.mono (Nat.le_refl _) (by omega_arith))
  have f₁ : Frm B (allRanges W) s.mem s₁.mem := Frm.of_outside o₁ (by simp [allRanges])
  have h₁ := h.congr f₁ (fun _ hr => all_mut hr) (k₀.trans kS) (by decide)
  have M₁ : wv s₁.mem B (slot W aM) (W / 2) = wv s.mem B (slot W aM) (W / 2) :=
    o₁.wv (by omega_arith) (by omega_arith)
  have top₁ : word s₁.mem B (slot W aM + 8 * (W / 2 - 1)) = word s.mem B (slot W aM + 8 * (W / 2 - 1)) :=
    o₁.word (by omega_arith) (by omega_arith)
  have D₁ : wv s₁.mem B (slot W aD) W = wv s.mem B (slot W aD) W :=
    o₁.wv (by omega_arith) (by omega_arith)
  -- the remainder's words: the seed below `W / 2 - 1`, zero from there
  have zS : ∀ i, W / 2 - 1 ≤ i → i < W + 2 → word s₁.mem B (slot W aR + 8 * i) = 0 := fun i h1 h2 => by
    rw [oS.word (.inr (by omega_arith)) (by omega_arith)]
    exact (wv_eq_zero_iff _ _ _ _).mp z₀ i h2
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
  have k03 := ((k₀.trans kS).trans k₂).trans k₃
  have h₃ := h₁.congr f₃ (fun _ hr => all_mut hr) (k₂.trans k₃) (by decide)
  refine WP.seq (WP.mono (countSetup_ok h₃ hZ (top := top) (fun k e => by have := hk k e; omega_arith))
    fun s₄ ⟨ha, m₄, k₄⟩ => ?_)
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
  have R₄ : ∀ n, n ≤ W + 2 → wv s₄.mem B (slot W aR) n = wv s₁.mem B (slot W aR) n := fun n hn' => by
    rw [o₄.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith)]
  have zhi : wv s₄.mem B (slot W aR + 8 * (W / 2)) (W + 2 - W / 2) = 0 := by
    rw [o₄.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith)]
    exact wv_zero fun i hi => by rw [Nat.add_assoc, ← Nat.mul_add]; exact zS _ (by omega_arith) (by omega_arith)
  -- the remainder starts as the seed, below the divisor
  have z1 : wv s₄.mem B (slot W aR + 8 * (W / 2 - 1)) 1 = 0 := by
    rw [o₄.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith)]
    exact wv_zero fun i hi => by
      rw [Nat.add_assoc, ← Nat.mul_add]; exact zS _ (by omega_arith) (by omega_arith)
  have e1 := wv_add s₄.mem B (slot W aR) (W / 2 - 1) 1
  rw [show W / 2 - 1 + 1 = W / 2 by omega_arith, z1, Nat.mul_zero, Nat.add_zero] at e1
  have Mlo : 2 ^ (64 * (W / 2 - 1)) ≤ wv s₄.mem B (slot W aM) (W / 2) := by
    have t := (R2w.top_half s₄.mem B (slot W aM) (W / 2 - 1)).mpr (by rw [eqTop]; exact hd)
    rw [show W / 2 - 1 + 1 = W / 2 by omega_arith] at t
    have : 2 ^ (64 * (W / 2 - 1)) ≤ 2 ^ (64 * (W / 2)) / 2 := by
      rw [show 64 * (W / 2) = 64 * (W / 2 - 1) + 63 + 1 by omega_arith, Nat.pow_succ, Nat.mul_div_cancel _ (by decide),
        Nat.pow_add]
      exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    omega_arith
  have R₀lt : wv s₄.mem B (slot W aR) (W / 2) < wv s₄.mem B (slot W aM) (W / 2) :=
    Nat.lt_of_lt_of_le (by rw [e1]; exact wv_lt _ _ _ _) Mlo
  -- the dividend's words below `j` after the remainder so far
  let R₀ := wv s₄.mem B (slot W aR) (W / 2)
  let P : Nat → Nat := fun j => R₀ * 2 ^ (64 * (j0 W top - j)) + wv s₄.mem B (slot W aD + 8 * j) (j0 W top - j)
  have hP : ∀ j, 1 ≤ j → j ≤ j0 W top →
      P (j - 1) = (word s₄.mem B (slot W aD + 8 * (j - 1))).toNat + 2 ^ 64 * P j := fun j h1 h2 => by
    simp only [P]
    have ew := wv_add s₄.mem B (slot W aD + 8 * (j - 1)) 1 (j0 W top - j)
    rw [show 1 + (j0 W top - j) = j0 W top - (j - 1) by omega_arith,
      show slot W aD + 8 * (j - 1) + 8 * 1 = slot W aD + 8 * j by omega_arith] at ew
    rw [ew, show j0 W top - (j - 1) = (j0 W top - j) + 1 by omega_arith, Nat.mul_add, Nat.pow_add]
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.pow_zero, Nat.one_mul]
    rw [show 2 ^ (64 * 1) = 2 ^ 64 from rfl, Nat.mul_add]
    ac_rfl
  have h0 : wv s₄.mem B (slot W aR) (W / 2) = P (j0 W top) % wv s₄.mem B (slot W aM) (W / 2) := by
    simp only [P, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, wv, Nat.add_zero]
    exact (Nat.mod_eq_of_lt R₀lt).symm
  refine WP.mono (loop_ok h₄ hZ hW hj1 (by omega_arith) (by rw [m₄, word_writeW_self]) ha (by rw [eqTop]; exact hd)
    (by rw [o₄.word (d := slot W aV) (Or.inl (by omega_arith)) (by omega_arith), m₃, m₂, word_writeW_self,
          BitVec.toNat_ofNat, eqTop];
        rw [Nat.mod_eq_of_lt (reciprocal_lt (by rw [top₁]; exact hd)), top₁])
    P hP h0 (by rw [eqM]; exact hMpos)) fun t ⟨v, fl, kl⟩ => ?_
  have hi : wv t.mem B (slot W aR + 8 * (W / 2)) (W + 1 - W / 2) = 0 := by
    have zh' := wv_eq_zero_iff _ _ _ _ |>.mp zhi
    apply wv_zero
    intro i hi
    rw [fl.word_eq (by
      intro r hr
      simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [slot, aR, aT, aV] <;> omega_arith) (by omega_arith)]
    exact zh' i (by omega_arith)
  refine ⟨fun hX => ?_, ?_, ((k03.trans k₄).trans kl).mono (by decide)⟩
  · -- the seed is the dividend's words from `j₀`, so `P 0` is the dividend
    have hX₄ : wv s₄.mem B (slot W aD) W < 2 ^ (64 * xw W top) := by rw [eqD]; exact hX
    obtain ⟨pfx, -⟩ := seeded_prefix s₄.mem B (d := slot W aD) hj hxw hX₄
    have Dj : wv s₄.mem B (slot W aD + 8 * j0 W top) (W / 2 - 1) =
        wv s₀.mem B (slot W aD + 8 * j0 W top) (W / 2 - 1) := by
      rw [o₄.wv (.inl (by simp only [slot, aD, aV]; omega_arith)) (by omega_arith),
        o₃.wv (.inl (by simp only [slot, aD, aV]; omega_arith)) (by omega_arith),
        oS.wv (.inr (by simp only [slot, aD, aR]; omega_arith)) (by omega_arith)]
    have seedv : R₀ = wv s₄.mem B (slot W aD + 8 * j0 W top) (W - j0 W top) := by
      simp only [R₀]; rw [e1, R₄ _ (by omega_arith), v₁, ← Dj, pfx]
    have P0 : P 0 = wv s₄.mem B (slot W aD) W := by
      simp only [P, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
      have ed := wv_add s₄.mem B (slot W aD) (j0 W top) (W - j0 W top)
      rw [show j0 W top + (W - j0 W top) = W by omega_arith, ← seedv] at ed
      rw [ed, Nat.add_comm, Nat.mul_comm]
    have := wv_add t.mem B (slot W aR) (W / 2) (W + 1 - W / 2)
    rw [show W / 2 + (W + 1 - W / 2) = W + 1 by omega_arith, hi, Nat.mul_zero, Nat.add_zero] at this
    rw [this, v, P0, eqD, eqM, Nat.add_zero]
  · apply ((f₁.trans f₃).trans f₄).trans
    apply cover fl
    intro r hr
    simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨(slot W aR, 8 * (W + 2)), by simp [allRanges], (Nat.le_refl _), by omega_arith⟩
    · exact ⟨(slot W aT, 8 * (W / 2 + 1)), by simp [allRanges], (Nat.le_refl _), (Nat.le_refl _)⟩
    · exact ⟨(slot W aV, 24), by simp [allRanges], by omega_arith, by omega_arith⟩

end VG.Proof.Rsa.X86_64.WordDivide
