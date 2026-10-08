import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase

/-!
# The window method on AArch64: the complete addition into `R`

`R = R + E` by the complete addition into `D`, then copied (`winAdd_ok`), as a step
of the loop (`sumStep_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-! ## The complete addition into `R` -/

/-- After a sum into `D` copied to `R`: `R` holds `v`, the sum's value. -/
structure SumPostW (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (v : Fe C × Fe C × Fe C)
    (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base ((winOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]) s.mem s'.mem
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p
  val : (tmv C K.M.n base s' K.R.x, tmv C K.M.n base s' K.R.y, tmv C K.M.n base s' K.R.z) = v
/-- A sum into `D` (the field program `ops`, writing `rcbW K.S K.D` and computing `v`),
then copied to `R`. -/
theorem winCopy_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) {ops : List FOp} {V : List Nat} {E' : Nat → Fe C} {v : Fe C × Fe C × Fe C}
    {s : State} (hs : Scr s base size)
    (W : WP isa (fprogB K.M ops) s fun s' => ProgKeep K.M base (rcbW K.S K.D) s s' ∧
      Inv K.M base size C.p (· ∈ winSlots K) ([K.D.x, K.D.y, K.D.z] ++ V) E' s' ∧
      (E' K.D.x, E' K.D.y, E' K.D.z) = v) :
    WP isa (.seq (fprogB K.M ops) (.block (copyPt K.M.n K.R K.D))) s (SumPostW K C base size v s) := by
  have hn := hs.nowrap
  refine WP.seq (WP.mono W fun s₁ h₁ => ?_)
  obtain ⟨k₁, I₁, v₁⟩ := h₁
  obtain ⟨rxy, rxz, ryz, hRD, -, -, -, -, -, hD⟩ := hL.other_ne
  simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hD
  have hRD' : ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ y ∈ [K.D.x, K.D.y, K.D.z], x ≠ y := by
    intro x hx y hy e
    subst e
    refine hRD x hx (List.mem_append_right _ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> simp [rcbW]
  have wR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winWs K := fun x hx => winOther_ws K x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_in)
  have wD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winWs K := fun x hx => winOther_ws K x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_in)
  have ap : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z],
      ∀ y ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy hxy
    have hw : ∀ z ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], z ∈ winWs K := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h | h | h | h | h
      · exact wR z (by simp [h])
      · exact wR z (by simp [h])
      · exact wR z (by simp [h])
      · exact wD z (by simp [h])
      · exact wD z (by simp [h])
      · exact wD z (by simp [h])
    exact hL.apart₂ (hw x hx) (hw y hy) hxy
  have rd : ∀ {x y}, x ∈ [K.R.x, K.R.y, K.R.z] → y ∈ [K.D.x, K.D.y, K.D.z] → x ≠ y := fun hx hy =>
    hRD' _ hx _ hy
  have axd := ap K.R.x (by simp) K.D.x (by simp) (rd (by simp) (by simp))
  have ayd := ap K.R.y (by simp) K.D.y (by simp) (rd (by simp) (by simp))
  have azd := ap K.R.z (by simp) K.D.z (by simp) (rd (by simp) (by simp))
  have axy := ap K.R.x (by simp) K.R.y (by simp) rxy
  have axz := ap K.R.x (by simp) K.R.z (by simp) rxz
  have ayz := ap K.R.y (by simp) K.R.z (by simp) ryz
  have dyax := ap K.D.y (by simp) K.R.x (by simp) (Ne.symm (rd (by simp) (by simp)))
  have dzax := ap K.D.z (by simp) K.R.x (by simp) (Ne.symm (rd (by simp) (by simp)))
  have dzay := ap K.D.z (by simp) K.R.y (by simp) (Ne.symm (rd (by simp) (by simp)))
  have le : ∀ x ∈ winOther K, x + 8 * K.M.n ≤ size := fun x hx => hL.lay.le x (winOther_mem hx)
  have al : ∀ x ∈ winOther K, x % 8 = 0 := fun x hx => hA.sl x (winOther_mem hx)
  have b64 : ∀ x ∈ winOther K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have hs₁ := k₁.scr hs
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  have W2 := copy_ok K.M.n hs₁ (le _ (by win_in)) (le _ (by win_in)) (al _ (by win_in))
    (al _ (by win_in)) (o := K.R.x) (a := K.D.x) (axd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W3 := copy_ok K.M.n hs₂ (le _ (by win_in)) (le _ (by win_in)) (al _ (by win_in))
    (al _ (by win_in)) (o := K.R.y) (a := K.D.y) (ayd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have W4 := copy_ok K.M.n hs₃ (le _ (by win_in)) (le _ (by win_in)) (al _ (by win_in))
    (al _ (by win_in)) (o := K.R.z) (a := K.D.z) (azd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄, O₄⟩ := h₄
  have hDx : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  have hDy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  have hDz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  have bAx := b64 K.R.x (by win_in)
  have bAy := b64 K.R.y (by win_in)
  have bAz := b64 K.R.z (by win_in)
  have bDy := b64 K.D.y (by win_in)
  have bDz := b64 K.D.z (by win_in)
  have wx : wordsVal s₄.mem base K.R.x K.M.n = wordsVal s₁.mem base K.D.x K.M.n := by
    rw [O₄.wordsVal axz bAx, O₃.wordsVal axy bAx, e₂]
  have wy : wordsVal s₄.mem base K.R.y K.M.n = wordsVal s₁.mem base K.D.y K.M.n := by
    rw [O₄.wordsVal ayz bAy, e₃, O₂.wordsVal dyax bDy]
  have wz : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s₁.mem base K.D.z K.M.n := by
    rw [e₄, O₃.wordsVal dzay bDz, O₂.wordsVal dzax bDz]
  refine ⟨hs₃.of_keepRegs k₄ (by decide), ?_, ?_, ?_, ?_⟩
  · have c1 : ∀ r ∈ [Reg.x1], r ∈ clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
    exact ((⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩ : KeepRegs (clob K.M.n) s s₁).trans
      ((k₂.mono c1).trans ((k₃.mono c1).trans (k₄.mono c1))))
  · refine (k₁.unch.trans (O₂.unch.trans (O₃.unch.trans O₄.unch))).mono ?_
    intro w hw
    simp only [winOther, rcbW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.cons_append, List.nil_append] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [wx]; exact I₁.lt _ hDx
    · rw [wy]; exact I₁.lt _ hDy
    · rw [wz]; exact I₁.lt _ hDz
  · rw [← v₁]
    show (toM _ _ _, toM _ _ _, toM _ _ _) = _
    rw [wx, wy, wz, I₁.val _ hDx, I₁.val _ hDy, I₁.val _ hDz]

/-- `R = R + E` by Algorithm 4 into `D`, then copied. -/
theorem winAdd_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.R K.E, wordsVal s.mem base x K.M.n < C.p) :
    WP isa (.seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))) s
      (SumPostW K C base size (VG.Proof.Weierstrass.rcbAdd3 (tmv C K.M.n base s K.S.b3)
        (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
        (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)) s) := by
  have hLo : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ winRo K ++ winOther K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_right _ (List.mem_append_right _ hx)
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> win_in
  have hO : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ winSlots K := fun x hx =>
    List.mem_append_left _ (hLo x hx)
  have hI : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) (tmv C K.M.n base s) s :=
    ⟨hs, hM, fun x hx => hO x (List.mem_append_right _ hx), hlt, fun _ _ => rfl⟩
  exact winCopy_ok hL hA hs
    (rcb3_ok hL.lay hA.al hp (hL.rcbApart_D (Or.inr rfl)) hO (hA.low hLo) hI (fun x hx => hx))

/-- `R = R + E`, for `R` representing `PR` and `E` `PQ`. -/
theorem sumStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    {s₀ s : State} (hF : WinFixed K C base s₀ P k) (hS : WinSt K C base size P s₀ s)
    {PR PQ : Point C} (hPR : onCurve C PR = true) (hPQ : onCurve C PQ = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltq : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) PR)
    (hQ : Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) PQ) :
    WP isa (.seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))) s fun s' =>
      WinSt K C base size P s₀ s' ∧ s'.gpr .x19 = s.gpr .x19 ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (Spec.Weierstrass.add PR PQ) := by
  obtain ⟨-, tb, ro_lt, -⟩ := hS.ro_tmv hL hF
  have hlt : ∀ x ∈ rcbR K.S K.R K.E, wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · exact hltR _ (by simp)
    · exact hltR _ (by simp)
    · exact hltR _ (by simp)
    · exact hltq _ (by simp)
    · exact hltq _ (by simp)
    · exact hltq _ (by simp)
  refine WP.mono (winAdd_ok hL hA hp hS.scr hS.mod hlt) fun s' S => ?_
  have hV := S.val
  rw [tb] at hV
  exact ⟨hS.next hL S.scr (S.keep.mono clob_combClob) S.unch, S.keep.gpr _ (x19_not_clob _), S.lt,
    hC.add3 hM3 hPR hPQ hR hQ hV.symm⟩

end VG.Proof.Weierstrass.AArch64
