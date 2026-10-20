module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State

import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- `R` in projective coordinates, through `E`, `(0 : 1 : 0)` for `O`. -/
theorem jointFinish_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    {P : Point C} {s₀ s : State} (hF : NafFixed K C base s₀ P k) {A : Point C}
    (h : NSt K C base size P s₀ s)
    (Rl : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (RJ : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      A) :
    WP isa (finish K) s fun t => NSt K C base size P s₀ t ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal t.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y) (tmv C K.M.n base t K.R.z)
        A := by
  have hW := hL.win
  have hn := h.scr.nowrap
  obtain ⟨-, -, -, -, -, -, a7, a8⟩ := rcbApart_naf hW
  have sR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (R_other K x hx)
  have sE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (E_other K x hx)
  have sZ : ∀ x ∈ [(WinCfg.zeroPt K).x, (WinCfg.zeroPt K).y, (WinCfg.zeroPt K).z],
      x ∈ winRo K ++ winOther K := by
    intro x hx
    simp only [WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx; exact List.mem_append_left _ (by simp [winRo])
  obtain ⟨rol, hz⟩ := h.ro hW hF
  -- `E = R`.
  let V := winRo K ++ [K.R.x, K.R.y, K.R.z]
  have hVs : ∀ x ∈ V, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · exact winOther_mem (R_other K x hx)
  have hVl : ∀ x ∈ V, wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact rol x hx
    · exact Rl x hx
  have hRV : ∀ x ∈ rcbR K.S (WinCfg.zeroPt K) K.R, x ∈ V := by
    intro x hx
    simp only [rcbR, WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> simp [V, winRo]
  have sl := winJ_sl (o := K.E) (p := WinCfg.zeroPt K) (q := K.R) (E_other K) sZ sR
  rw [finish]
  refine WP.seq (WP.mono (copyPointJ_ok hW.lay hL.al.al a7 sl.1 (inv_of h.scr h.mod hVs hVl) hRV RJ)
    fun s₁ h₁ => ?_)
  obtain ⟨sc₁, k₁, U₁, M₁, El, EJ, Vl₁, -⟩ := jacPost_frame hW h.scr h.mod (Or.inr (Or.inr rfl)) h₁
  have S₁ := h.next hW sc₁ (k₁.mono clob_nafClob) U₁
  -- `R = fromJ E`.
  let V₁ := winRo K ++ [K.E.x, K.E.y, K.E.z]
  have hV₁s : ∀ x ∈ V₁, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · exact winOther_mem (E_other K x hx)
  have hV₁l : ∀ x ∈ V₁, wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Vl₁ x (List.mem_append_left _ hx)
    · exact El x hx
  have hRV₁ : ∀ x ∈ rcbR K.S K.E (WinCfg.zeroPt K), x ∈ V₁ := by
    intro x hx
    simp only [rcbR, WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> simp [V₁, winRo]
  have w4 := winJ_sl (o := K.R) (p := K.E) (q := WinCfg.zeroPt K) (R_other K) sE sZ
  rw [fromJ_eq]
  refine WP.seq (WP.mono (winN_ok hW hL.al hp fromJN_ok a8 w4.1 w4.2.1 w4.2.2
    (inv_of sc₁ M₁ hV₁s hV₁l) hRV₁) fun s₂ ⟨k₂, U₂, E₂, I₂, o₂, v₂⟩ => ?_)
  have S₂ := S₁.next hW I₂.scr (k₂.mono clob_nafClob) U₂
  have z₁ : tmv C K.M.n base s₁ K.zero = 0 := by
    have := (S₁.ro hW hF).2
    show toM _ _ _ = 0; rw [this]; exact toM_zero _ _
  have r₂ : (E₂ K.R.x, E₂ K.R.y, E₂ K.R.z) = (tmv C K.M.n base s₁ K.E.x * tmv C K.M.n base s₁ K.E.z,
      tmv C K.M.n base s₁ K.E.y + tmv C K.M.n base s₁ K.zero,
      tmv C K.M.n base s₁ K.E.z * tmv C K.M.n base s₁ K.E.z * tmv C K.M.n base s₁ K.E.z) :=
    v₂.trans (fromJN_run _)
  simp only [z₁, Prod.mk.injEq] at r₂
  have ez : E₂ K.E.z = tmv C K.M.n base s₁ K.E.z := o₂ _ (a8.apart _ (by simp [rcbR]))
  have hRl : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₂.mem base x K.M.n < C.p :=
    fun x hx => I₂.lt x (List.mem_append_left _ hx)
  have hEz : wordsVal s₂.mem base K.E.z K.M.n < C.p :=
    I₂.lt _ (List.mem_append_right _ (by simp [V₁]))
  -- `Y = 1` where `Z = 0`.
  refine WP.mono (ySel_ok hW hL.al S₂.scr (Nat.lt_trans hone_lt hpn)) fun t ⟨vt, kt, Ut⟩ => ?_
  have hRy : K.R.y ∈ winOther K := by win_in
  have St := S₂.next hW (S₂.scr.of_keepRegs kt (by decide)) (kt.mono fun r hr => nafClob_mem (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
    (Ut.mono fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact List.mem_append_left _ (List.mem_map_of_mem hRy))
  obtain ⟨rxy, -, ryz, -⟩ := hW.other_ne
  have hws : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winWs K := fun x hx => winOther_ws K x (R_other K x hx)
  have eR : ∀ x ∈ [K.R.x, K.R.z], x ≠ K.R.y →
      wordsVal t.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx hne
    have hxw : x ∈ winWs K := hws x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h <;> simp [h])
    refine Ut.wordsVal (fun w hw => ?_) (by have := hW.lay.le x (winWs_slots K x hxw); omega_using [hn, this])
    rw [List.mem_singleton.mp hw]
    exact hW.apart₂ hxw (hws _ (by simp)) hne
  have ex₂ := eR K.R.x (by simp) rxy
  have ez₂ := eR K.R.z (by simp) (Ne.symm ryz)
  have tm : ∀ {x}, wordsVal t.mem base x K.M.n = wordsVal s₂.mem base x K.M.n →
      tmv C K.M.n base t x = tmv C K.M.n base s₂ x := fun h => by
    show toM _ _ _ = toM _ _ _; rw [h]
  have vx : tmv C K.M.n base s₂ K.R.x = tmv C K.M.n base s₁ K.E.x * tmv C K.M.n base s₁ K.E.z :=
    (I₂.val _ (by simp)).trans r₂.1
  have vy : tmv C K.M.n base s₂ K.R.y = tmv C K.M.n base s₁ K.E.y :=
    (I₂.val _ (by simp)).trans (r₂.2.1.trans (by grind))
  have vz : tmv C K.M.n base s₂ K.R.z =
      tmv C K.M.n base s₁ K.E.z * tmv C K.M.n base s₁ K.E.z * tmv C K.M.n base s₁ K.E.z :=
    (I₂.val _ (by simp)).trans r₂.2.2
  have vE : tmv C K.M.n base s₂ K.E.z = tmv C K.M.n base s₁ K.E.z :=
    (I₂.val _ (by simp [V₁])).trans ez
  have hZ : (wordsVal s₂.mem base K.E.z K.M.n = 0) ↔ tmv C K.M.n base s₁ K.E.z = 0 := by
    rw [← vE, toM_eq_zero_iff hp hEz]
  have ey₂ : tmv C K.M.n base t K.R.y =
      if tmv C K.M.n base s₁ K.E.z = 0 then 1 else tmv C K.M.n base s₁ K.E.y := by
    by_cases hz0 : wordsVal s₂.mem base K.E.z K.M.n = 0
    · have e₂ : wordsVal t.mem base K.R.y K.M.n = K.one := by rw [vt]; simp only [hz0, ↓reduceIte]
      show toM _ _ _ = _
      rw [e₂, hone]; simp only [hZ.mp hz0, ↓reduceIte]
    · have e₂ : wordsVal t.mem base K.R.y K.M.n = wordsVal s₂.mem base K.R.y K.M.n := by
        rw [vt]; simp only [hz0, ↓reduceIte]
      rw [tm e₂, vy]
      exact (ite_eq_right_iff.mpr fun h' => absurd (hZ.mpr h') hz0).symm
  refine ⟨St, fun x hx => ?_, ?_⟩
  · rcases mem3 hx with rfl | rfl | rfl
    · rw [ex₂]; exact hRl _ (by simp)
    · rw [vt]; split
      · exact hone_lt
      · exact hRl _ (by simp)
    · rw [ez₂]; exact hRl _ (by simp)
  · rw [tm ex₂, ey₂, tm ez₂, vx, vz]
    exact InvJ.out hC EJ

end VG.Proof.Weierstrass.AArch64.PubNaf
