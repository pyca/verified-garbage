import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry

/-!
# The Jacobian window method on x86-64: an iteration

`R = 32 R + [d_j]P`: the doublings (`dbls_ok`), digit `j`'s entry
(`jentry_ok`), `D = R + T` (`cadd_ok`), then `D = T` where `R = O` and `R = D`
unless the digit is zero (`jmask_ok`). The result is a Jacobian triple of
`[winE k' J j]P` (`jstep_point`): the addition is not exceptional
(`Window5.loop_noexc`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-! ## The point -/

/-- The iteration's result: `R` for a zero digit, else `T` where `R = O`, else
the Jacobian sum, a triple of `[winE k' J i]P`. -/
theorem jstep_point (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : C.n % 32 = 17) (hn64 : 64 ≤ C.n) {k J i : Nat} (hk : k < C.n)
    (hi : i < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C}
    (h1 : InvJ C X1 Y1 Z1 (mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P))
    (h2 : 1 ≤ magH 16 (Window5.nib (k + 16 * Window5.geom J) i) →
      InvJ C X2 Y2 Z2 (Window5.winPt C P (k + 16 * Window5.geom J) i) ∧ Z2 ≠ 0) :
    InvJ C
      (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then X1
        else if Z1 = 0 then X2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).1)
      (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Y1
        else if Z1 = 0 then Y2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1)
      (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Z1
        else if Z1 = 0 then Z2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2)
      (mul (Window5.winE (k + 16 * Window5.geom J) J i) P) := by
  have hadd := Window5.win_add hC hP (k := k + 16 * Window5.geom J) (J := J) (j := i) (Nat.le_add_left _ _) hi
  generalize hk' : k + 16 * Window5.geom J = k' at hadd h1 h2 ⊢
  generalize he : Window5.winE k' J (i + 1) = e at hadd h1
  rw [← hadd]
  by_cases h0 : magH 16 (Window5.nib k' i) = 0
  · simp only [h0, ↓reduceIte]
    rw [Window5.winPt_zero h0, add_infinity]
    exact h1
  · simp only [h0, ↓reduceIte]
    obtain ⟨J2, z2⟩ := h2 (by omega)
    have hQ := hC.onCurve_mul hP (32 * e)
    have hW : onCurve C (Window5.winPt C P k' i) = true := Window5.onCurve_winPt hC hP k' i
    by_cases hz : Z1 = 0
    · simp only [hz, ↓reduceIte]
      rw [(h1.z_zero_iff hC).mp hz, infinity_add']
      exact J2
    · simp only [hz, ↓reduceIte]
      have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with rfl | h
        · exact absurd ((h1.z_zero_iff hC).mpr (by rw [Nat.mul_zero, Window5.mul_zero_pt])) hz
        · exact h
      rw [← he, ← hk'] at he1
      obtain ⟨ne1, ne2⟩ := Window5.loop_noexc hC hO hP hP0 hn17 hn64 hk hi he1
      rw [hk', he] at ne1 ne2
      have hh : X2 * (Z1 * Z1) - X1 * (Z2 * Z2) ≠ 0 := by
        intro hx
        by_cases hy : Y2 * Z1 * (Z1 * Z1) - Y1 * Z2 * (Z2 * Z2) = 0
        · exact ne1 (h1.same hC J2 hz z2 hx hy)
        · exact ne2 (h1.opposite hC hQ hW J2 hz z2 hx hy)
      exact h1.add_ne hC hM3 hQ hW J2 hz z2 hh

/-- The iteration's result for any `k`: a triple of a point of the curve, which
is `[winE k' J i]P` for `k < n` (`jstep_point`). Beyond `n` an addition may be
exceptional: then `Z = 0`, a triple of `O`. -/
theorem jstep_pt (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : C.n % 32 = 17) (hn64 : 64 ≤ C.n) {k J i : Nat}
    (hi : i < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {Q1 : Point C} (hQ1 : onCurve C Q1 = true)
    (hQ1e : k < C.n → Q1 = mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P)
    (h1 : InvJ C X1 Y1 Z1 Q1)
    (h2 : 1 ≤ magH 16 (Window5.nib (k + 16 * Window5.geom J) i) →
      InvJ C X2 Y2 Z2 (Window5.winPt C P (k + 16 * Window5.geom J) i) ∧ Z2 ≠ 0) :
    ∃ Q : Point C, onCurve C Q = true ∧ (k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom J) J i) P) ∧
      InvJ C
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then X1
          else if Z1 = 0 then X2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Y1
          else if Z1 = 0 then Y2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Z1
          else if Z1 = 0 then Z2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2) Q := by
  by_cases hk : k < C.n
  · refine ⟨_, hC.onCurve_mul hP _, fun _ => rfl, ?_⟩
    rw [hQ1e hk] at h1
    exact jstep_point hC hM3 hO hP hP0 hn17 hn64 hk hi h1 h2
  have nk : ∀ Q : Point C, k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom J) J i) P :=
    fun _ h' => absurd h' hk
  generalize k + 16 * Window5.geom J = k' at h2 nk ⊢
  by_cases h0 : magH 16 (Window5.nib k' i) = 0
  · simp only [h0, ↓reduceIte]
    exact ⟨Q1, hQ1, nk _, h1⟩
  · simp only [h0, ↓reduceIte]
    obtain ⟨J2, z2⟩ := h2 (by omega)
    have hW : onCurve C (Window5.winPt C P k' i) = true := Window5.onCurve_winPt hC hP k' i
    by_cases hz : Z1 = 0
    · simp only [hz, ↓reduceIte]
      exact ⟨_, hW, nk _, J2⟩
    · simp only [hz, ↓reduceIte]
      by_cases hh : X2 * (Z1 * Z1) - X1 * (Z2 * Z2) = 0
      · refine ⟨.infinity, rfl, nk _, Or.inl ⟨rfl, ?_⟩⟩
        show Z1 * Z2 * (X2 * (Z1 * Z1) - X1 * (Z2 * Z2)) = 0
        rw [hh]; grind
      · exact ⟨_, hC.onCurve_add hQ1 hW, nk _, h1.add_ne hC hM3 hQ1 hW J2 hz z2 hh⟩

/-! ## The masks -/

/-- `D = T` where `R`'s `Z` is zero, and `R = D` unless digit `i` is zero. -/
theorem jmask_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) {s : State} {i : Nat} (hi : i < K.J)
    (hf : JFrame K C base size s₀ s) (hb : s.gpr .rbx = BitVec.ofNat 64 i) :
    WP isa (.block (nzMask K.M.n K.R.z ++ selPt K.M.n K.D K.E K.D ++ K.tc.digit ++ eqMask 0 ++
      selPt K.M.n K.R K.D K.R ++ ([.alu .test .rbx (.reg .rbx)] : List Instr))) s fun t =>
      JFrame K C base size s₀ t ∧ Unch base (jwLoopW K) s.mem t.mem ∧ t.gpr .rbx = BitVec.ofNat 64 i ∧
      t.zf = some (decide (i = 0)) ∧
      ∀ c < 3, wordsVal t.mem base ([K.R.x, K.R.y, K.R.z].getD c 0) K.M.n =
        if magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i) = 0 then
          wordsVal s.mem base ([K.R.x, K.R.y, K.R.z].getD c 0) K.M.n
        else if wordsVal s.mem base K.R.z K.M.n = 0 then
          wordsVal s.mem base ([K.E.x, K.E.y, K.E.z].getD c 0) K.M.n
        else wordsVal s.mem base ([K.D.x, K.D.y, K.D.z].getD c 0) K.M.n := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hnn := hL.n0
  have hbl := hL.bits
  obtain ⟨mx, my, mz, -, -⟩ := hL.T_mem
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  have ap := fun {x y : Nat} (hx : x ∈ jwSlots K) (hy : y ∈ jwSlots K) (h : x ≠ y) => hL.ap hx hy h
  have hDE : ∀ x ∈ [K.D.x, K.D.y, K.D.z], ∀ y ∈ [K.E.x, K.E.y, K.E.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    have hxo : x ∈ jwOther K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
    simp only [hL.Tx, hL.Ty, hL.Tz, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> exact hL.jg_apart (List.mem_append_right _ hxo) (by decide)
  have hRD : ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ y ∈ [K.D.x, K.D.y, K.D.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact hL.ap_oth (i := 0) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 5) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 5) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 5) (by decide) (by decide) (by decide)
  have dd := And.intro (hL.ap_oth (i := 3) (j := 4) (by decide) (by decide) (by decide))
    (And.intro (hL.ap_oth (i := 3) (j := 5) (by decide) (by decide) (by decide))
      (hL.ap_oth (i := 4) (j := 5) (by decide) (by decide) (by decide)))
  have rr := And.intro (hL.ap_oth (i := 0) (j := 1) (by decide) (by decide) (by decide))
    (And.intro (hL.ap_oth (i := 0) (j := 2) (by decide) (by decide) (by decide))
      (hL.ap_oth (i := 1) (j := 2) (by decide) (by decide) (by decide)))
  have le : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hL.le (by jw_mem)
  have leE : ∀ x ∈ [K.D.x, K.D.y, K.D.z, K.E.x, K.E.y, K.E.z], x + 8 * K.M.n ≤ size := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.le (by jw_mem)
    · exact hL.le (by jw_mem)
    · exact hL.le (by jw_mem)
    · exact hL.le mx
    · exact hL.le my
    · exact hL.le mz
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs hnn (hL.le (by jw_mem : K.R.z ∈ jwSlots K))) fun s₁ ⟨c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₁ (decide (wordsVal s.mem base K.R.z K.M.n ≠ 0)) (by rw [c₁])
    (o := K.D) (a := K.E) leE dd hDE) fun s₂ ⟨dx, dy, dz, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [m₁] at dx dy dz O₂
  have UD : Unch base [(K.D.x, 8 * K.M.n), (K.D.y, 8 * K.M.n), (K.D.z, 8 * K.M.n)] s.mem s₂.mem :=
    fun x hx => O₂ x (hx (K.D.x, 8 * K.M.n) (by simp)) (hx (K.D.y, 8 * K.M.n) (by simp))
      (hx (K.D.z, 8 * K.M.n) (by simp))
  have F₂ := hf.next hL hs₂ (((Keeps.regs k₁).mono (sub_powClob (by decide))).trans
    (k₂.mono (sub_powClob (by decide)))) UD (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> exact mem_jwW_ws (other_ws (by jw_mem)))
  have hb₂ : s₂.gpr .rbx = BitVec.ofNat 64 i := by rw [k₂.gpr _ (by decide), k₁.1 _ (by decide), hb]
  rw [WP.block_append_iff]
  have hwj : 5 * i + 5 ≤ 5 * K.J := by omega
  have hbits₂ := F₂.bits hL hF
  refine WP.mono (digit_ok K.tc hs₂ (N := 5 * K.J) (by show 1 ≤ 5; decide) (by show 5 < 9; decide) hwj
    (by show K.bits + 5 * K.J ≤ size; omega) hb₂ hbits₂) fun s₃ ⟨_, r₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [show K.tc.w = 5 from rfl, Window5.combWin_five, show K.tc.H = 16 from rfl] at r₃
  have hm := magH_le (H := 16) (v := Window5.nib (k + JacWinCfg.offset K.J) i)
    (by have := Window5.nib_lt (k + JacWinCfg.offset K.J) i; omega)
  rw [WP.block_append_iff]
  refine WP.mono (eqMask_ok s₃ (v := 0) (by decide) (by omega) r₃) fun s₄ ⟨c₄, k₄, _⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₄ (decide (magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i) = 0))
    (by rw [c₄]) (o := K.R) (a := K.D) le rr hRD) fun s₅ ⟨rx, ry, rz, k₅, O₅⟩ => ?_
  have m₄ : s₄.mem = s₂.mem := by rw [k₄.2.1, k₃.2.1]
  rw [m₄] at rx ry rz O₅
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 i := by
    rw [k₅.gpr _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide), hb₂]
  refine WP.mono (testRbx_ok s₅ (by omega) hb₅) fun t ⟨z₆, k₆⟩ => ?_
  have m₆ : t.mem = s₅.mem := k₆.2.1
  have UR : Unch base [(K.R.x, 8 * K.M.n), (K.R.y, 8 * K.M.n), (K.R.z, 8 * K.M.n)] s₂.mem t.mem := by
    rw [m₆]; exact fun x hx => O₅ x (hx (K.R.x, 8 * K.M.n) (by simp)) (hx (K.R.y, 8 * K.M.n) (by simp))
      (hx (K.R.z, 8 * K.M.n) (by simp))
  have F₆ := F₂.next hL (hs₅.of_keeps k₆ (by decide)) (((((Keeps.regs k₃).mono (sub_powClob (by decide))).trans
    ((Keeps.regs k₄).mono (sub_powClob (by decide)))).trans (k₅.mono (sub_powClob (by decide)))).trans
    ((Keeps.regs k₆).mono (by simp))) UR (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> exact mem_jwW_ws (other_ws (by jw_mem)))
  have b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega
  -- `R` and `E` are not written by the first selection.
  have kR : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₂.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    refine UD.wordsVal (fun w hw => ?_) ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      have hw' : w.1 ∈ [K.D.x, K.D.y, K.D.z] ∧ w.2 = 8 * K.M.n := by rcases hw with rfl | rfl | rfl <;> simp
      rw [hw'.2]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hRD _ (by simp) _ hw'.1
      · exact hRD _ (by simp) _ hw'.1
      · exact hRD _ (by simp) _ hw'.1
      · exact (hDE _ hw'.1 _ (by simp)).symm
      · exact (hDE _ hw'.1 _ (by simp)).symm
      · exact (hDE _ hw'.1 _ (by simp)).symm
    · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact b64 _ (by jw_mem)
      · exact b64 _ (by jw_mem)
      · exact b64 _ (by jw_mem)
      · exact b64 _ mx
      · exact b64 _ my
      · exact b64 _ mz
  refine ⟨F₆, (UD.trans UR).mono fun w hw => ?_, by rw [k₆.1 _ (by simp), hb₅], z₆, fun c hc => ?_⟩
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> exact other_loopW (by jw_mem)
  · have : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases this with rfl | rfl | rfl
    · show wordsVal t.mem base K.R.x K.M.n = _
      rw [m₆, rx, dx, kR K.R.x (by simp)]
      by_cases h0 : magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i) = 0 <;>
        by_cases hz : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h0, hz]
    · show wordsVal t.mem base K.R.y K.M.n = _
      rw [m₆, ry, dy, kR K.R.y (by simp)]
      by_cases h0 : magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i) = 0 <;>
        by_cases hz : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h0, hz]
    · show wordsVal t.mem base K.R.z K.M.n = _
      rw [m₆, rz, dz, kR K.R.z (by simp)]
      by_cases h0 : magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i) = 0 <;>
        by_cases hz : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h0, hz]

end VG.Proof.Weierstrass.X86_64
