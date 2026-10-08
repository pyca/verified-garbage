import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStep

/-!
# The Jacobian window method on x86-64: an iteration

`JacWinCfg.step`: `rbx = j - 1`, `R = 32 R` (`dbls_ok`), digit `j - 1`'s entry
in `T` (`jentry_ok`), `D = R + T` (`cadd_ok`) and the masks (`jmask_ok`):
`R` then represents `[winE k' J (j - 1)]P` (`jstep_point`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- `16 Σ_{j<J} 32^j`. -/
theorem offset_eq (J : Nat) : JacWinCfg.offset J = 16 * Window5.geom J := by
  have := Window5.geom_mul J
  unfold JacWinCfg.offset
  omega

/-- The loop's invariant at `rbx = j`: `R` is a triple of a point of the curve,
`[winE k' J j]P` for `k < n`. -/
structure JInv (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k : Nat) (j : Nat) (s : State) : Prop where
  st : ∃ Q : Point C, onCurve C Q = true ∧
    (k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom K.J) K.J j) P) ∧
    RSt K C base size P s₀ Q s
  rbx : s.gpr .rbx = BitVec.ofNat 64 j

/-- `R`'s and `T`'s slots are apart from what `D = R + T` writes. -/
theorem cadd_apart (hL : JacWinLay K size) :
    ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z], ∀ y ∈ rcbW K.S K.D,
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
  intro x hx y hy
  have hyo : y ∈ jwOther K := by
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem
  simp only [hL.Tx, hL.Ty, hL.Tz, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hL.ap_oth (i := 0) (j := 7) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 8) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 9) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 10) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 11) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 12) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 5) (by decide) (by decide) (by decide)
  · simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hL.ap_oth (i := 1) (j := 7) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 8) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 9) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 10) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 11) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 12) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 5) (by decide) (by decide) (by decide)
  · simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hL.ap_oth (i := 2) (j := 7) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 8) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 9) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 10) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 11) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 12) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 5) (by decide) (by decide) (by decide)
  all_goals exact (hL.jg_apart (List.mem_append_right _ hyo) (by decide)).symm

/-- The masks' choice, in the field. -/
theorem tmv_sel {m0 : Prop} [Decidable m0] {n : Nat} {wz a b c : Nat}
    {Z A B D : Fe C} (hz : wz = 0 ↔ Z = 0)
    (ha : toM C.p (2 ^ (64 * n)) a = A) (hb : toM C.p (2 ^ (64 * n)) b = B)
    (hc : toM C.p (2 ^ (64 * n)) c = D) :
    toM C.p (2 ^ (64 * n)) (if m0 then a else if wz = 0 then b else c) =
      if m0 then A else if Z = 0 then B else D := by
  by_cases h0 : m0
  · simp [h0, ha]
  · by_cases h : wz = 0
    · simp [h0, h, hz.mp h, hb]
    · have hZ : ¬ Z = 0 := fun e => h (hz.mpr e)
      simp [h0, h, hZ, hc]

/-- An iteration, `1 ≤ j ≤ J`: `R = 32 R + [d_{j-1}]P`. -/
theorem jstep_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n)
    {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) {j : Nat}
    (hj1 : 1 ≤ j) (hjJ : j ≤ K.J) {s : State} (hI : JInv K C base size P s₀ k j s) :
    WP isa (K.step dbl).inline s fun s' => JInv K C base size P s₀ k (j - 1) s' ∧
      s'.zf = some (decide (j - 1 = 0)) := by
  obtain ⟨Q, hQ, hQe, R₀⟩ := hI.st
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  rw [JacWinCfg.step]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s hj1 (by omega) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have R₁ := R₀.rbxKeeps hL k₁
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dbls_ok hL hC hD hQ (j := j - 1) (by omega) b₁ R₁) fun s₂ ⟨R₂, b₂, _⟩ => ?_)
  refine WP.seq (WP.mono (jentry_ok hL hF (j := j - 1) (by omega) R₂.fr R₂.tbl b₂) fun s₃ h₃ =>
    WP.seq (WP.mono h₃ fun s₄ E₄ => ?_))
  -- `R` is not written by the entry.
  have hRe : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₄.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    have hxo : x ∈ jwOther K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
    refine E₄.unch.wordsVal (fun w hw => ?_) (by have := hL.le (other_mem hxo); omega)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
      exact hL.jg_apart (List.mem_append_right _ hxo) (by have := List.mem_range.mp hc; omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hL.ap_oth (i := 0) (j := 6) (by decide) (by decide) (by decide)
        · exact hL.ap_oth (i := 1) (j := 6) (by decide) (by decide) (by decide)
        · exact hL.ap_oth (i := 2) (j := 6) (by decide) (by decide) (by decide)
      · exact hL.lay.tmp x (other_mem hxo)
  have U₄ : Unch base (jwLoopW K) s₂.mem s₄.mem := E₄.unch.mono (jent_loopW K)
  -- `D = R + T`.
  have V₄ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n],
      x ∈ jwSlots K ∧ wordsVal s₄.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact E₄.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact E₄.lt 1 (by decide)⟩
    · exact ⟨mz, by rw [← tz]; exact E₄.lt 2 (by decide)⟩
    · exact ⟨m2, by rw [← t2]; exact E₄.lt 3 (by decide)⟩
    · exact ⟨m3, by rw [← t3]; exact E₄.lt 4 (by decide)⟩
  have I₄ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] (tmv C K.M.n base s₄) s₄ :=
    ⟨E₄.fr.scr, E₄.fr.mod, fun x hx => (V₄ x hx).1, fun x hx => (V₄ x hx).2, fun _ _ => rfl⟩
  have h2 := E₄.z2; have h3 := E₄.z3
  rw [t2, tz] at h2; rw [t3, t2, tz] at h3
  refine WP.seq (WP.mono (cadd_ok hL hp I₄ (fun x hx => hx) h2 h3) fun s₅ ⟨k₅, E₅, I₅, v₅⟩ => ?_)
  have U₅ : Unch base (jwLoopW K) s₄.mem s₅.mem := k₅.loopW (rcbW_loopW (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact other_loopW (by jw_mem)))
  have F₅ := E₄.fr.next hL (k₅.scr E₄.fr.scr) k₅.regs U₅ (jwLoopW_sub K)
  have hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (rbx_not_clob _), E₄.keep.gpr _ (rbx_not_clob _), b₂]
  -- `R` and `T` survive the addition.
  have keep₅ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₅.mem base x K.M.n = wordsVal s₄.mem base x K.M.n := by
    intro x hx
    have hv : x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h <;> simp [h]
    refine (ProgKeep.unch k₅).wordsVal (fun w hw => ?_) (by have := hL.le (V₄ x hv).1; omega)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
      exact cadd_apart hL x hx y hy
    · rw [List.mem_singleton.mp hw]; exact hL.lay.tmp x (V₄ x hv).1
  refine WP.mono (jmask_ok hL hF (i := j - 1) (by omega) F₅ hb₅) fun s₆ ⟨F₆, U₆, b₆, z₆, w₆⟩ => ?_
  rw [offset_eq] at w₆
  have ent := E₄.ent
  rw [offset_eq] at ent
  have R5 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base x K.M.n :=
    fun x hx => by
      rw [keep₅ x (List.mem_append_left [K.E.x, K.E.y, K.E.z] hx), hRe x hx]
  have T5 : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₅.mem base x K.M.n = wordsVal s₄.mem base x K.M.n :=
    fun x hx => keep₅ x (List.mem_append_right [K.R.x, K.R.y, K.R.z] hx)
  have hz : wordsVal s₅.mem base K.R.z K.M.n = 0 ↔ tmv C K.M.n base s₂ K.R.z = 0 := by
    rw [R5 _ (by simp)]; exact (toM_eq_zero_iff hp (R₂.lt _ (by simp))).symm
  have Dv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], tmv C K.M.n base s₅ x = E₅ x ∧
      wordsVal s₅.mem base x K.M.n < C.p := fun x hx =>
    ⟨I₅.val x (List.mem_append_left _ hx), I₅.lt x (List.mem_append_left _ hx)⟩
  have tvR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      tmv C K.M.n base s₂ x := fun x hx => by rw [R5 x hx]
  have tvT : ∀ x ∈ [K.E.x, K.E.y, K.E.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      tmv C K.M.n base s₄ x := fun x hx => by rw [T5 x hx]
  have tR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₂ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [hRe x hx]
  rw [tR _ (by simp), tR _ (by simp), tR _ (by simp)] at v₅
  have ex : tmv C K.M.n base s₆ K.R.x =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.x
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.x else E₅ K.D.x := by
    have w : wordsVal s₆.mem base K.R.x K.M.n = _ := w₆ 0 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.x (by simp)) (tvT K.E.x (by simp)) (Dv K.D.x (by simp)).1
  have ey : tmv C K.M.n base s₆ K.R.y =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.y
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.y else E₅ K.D.y := by
    have w : wordsVal s₆.mem base K.R.y K.M.n = _ := w₆ 1 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.y (by simp)) (tvT K.E.y (by simp)) (Dv K.D.y (by simp)).1
  have ez : tmv C K.M.n base s₆ K.R.z =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.z
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.z else E₅ K.D.z := by
    have w : wordsVal s₆.mem base K.R.z K.M.n = _ := w₆ 2 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.z (by simp)) (tvT K.E.z (by simp)) (Dv K.D.z (by simp)).1
  have vx := congrArg Prod.fst v₅
  have vy := congrArg (fun p => p.2.1) v₅
  have vz := congrArg (fun p => p.2.2) v₅
  dsimp only at vx vy vz
  rw [vx] at ex; rw [vy] at ey; rw [vz] at ez
  have hR := jstep_pt hC hM3 hO hP hP0 hn17 hn64 (k := k) (i := j - 1) (J := K.J) (by omega)
    (hC.onCurve_mul hQ 32) (fun hk => by
      rw [hQe hk, Window5.mul_mul hC hP, show j - 1 + 1 = j by omega]) R₂.rep
    (Z2 := tmv C K.M.n base s₄ K.E.z) (X2 := tmv C K.M.n base s₄ K.E.x) (Y2 := tmv C K.M.n base s₄ K.E.y)
    (fun h => by
      have J := ent h
      have j1 := J.jac
      have j2 := J.z
      rw [tx, ty, tz] at j1
      rw [tz] at j2
      exact ⟨j1, j2⟩)
  obtain ⟨Q', hQ', hQe', hR⟩ := hR
  refine ⟨⟨⟨Q', hQ', hQe', F₆, ((R₂.tbl.loopW hL U₄ hn (by decide)).loopW hL U₅ hn (by decide)).loopW hL U₆ hn (by decide),
    fun x hx => ?_, ?_⟩, b₆⟩, z₆⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have w : wordsVal s₆.mem base K.R.x K.M.n = _ := w₆ 0 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp)]; exact (V₄ _ (by simp)).2
        · exact (Dv _ (by simp)).2
    · have w : wordsVal s₆.mem base K.R.y K.M.n = _ := w₆ 1 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp)]; exact (V₄ _ (by simp)).2
        · exact (Dv _ (by simp)).2
    · have w : wordsVal s₆.mem base K.R.z K.M.n = _ := w₆ 2 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp)]; exact (V₄ _ (by simp)).2
        · exact (Dv _ (by simp)).2
  · rw [ex, ey, ez]
    exact hR

end VG.Proof.Weierstrass.X86_64
