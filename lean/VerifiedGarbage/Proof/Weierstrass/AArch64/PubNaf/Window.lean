module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Cache

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.StepD
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

/-!
# The public NAF multiplication

The table (`table_ok`), the `Z²` and `Z³` of its entries (`cacheTo_ok`),
`D = O` and the top digit, then `64 n` iterations
(`step_ok`) from `R = [r_{j+1}]P` to `R = [r_j]P`, for the residuals `r_j` of
the recoding (`Naf5.residual`), so that `R = [r_0]P = [k]P` in Jacobian
coordinates; then `R` in projective coordinates (`finish_ok`): `window_ok`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- `R` in projective coordinates, through `E`, `(0 : 1 : 0)` for `O`. -/
theorem finish_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    {P : Point C} {s₀ s : State} (hF : NafFixed K C base s₀ P k) {e : Nat}
    (h : NSt K C base size P s₀ s)
    (Rl : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (RJ : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (finish K) s fun t => NSt K C base size P s₀ t ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal t.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y) (tmv C K.M.n base t K.R.z)
        (mul e P) := by
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

/-- `D = O` and the count of the digits after the top one. -/
theorem head_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hone_lt : K.one < C.p) {P : Point C} {s₀ s₁ : State} (hF : NafFixed K C base s₀ P k)
    (S₁ : NSt K C base size P s₀ s₁) (hc : CacheOk K C base s₁) (hk : k < 2 ^ (64 * K.M.n)) :
    WP isa (.block (Jacobian.infinity K K.D ++
        ([.movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n)) 0] : List Instr))) s₁ fun s₃ =>
      NSt K C base size P s₀ s₃ ∧ CacheOk K C base s₃ ∧ s₃.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n) ∧
      (∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₃.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s₃ K.D.x) (tmv C K.M.n base s₃ K.D.y)
        (tmv C K.M.n base s₃ K.D.z) (mul (2 * Naf5.residual k (64 * K.M.n + 1)) P) := by
  have hW := hL.win
  have h6 := hL.n6
  rw [WP.block_append_iff]
  have hDs : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winSlots K := fun x hx => winOther_mem (D_other K x hx)
  refine WP.mono (infinityPoint_ok hW.lay hL.al.al hDs
    (inv_of S₁.scr S₁.mod (V := winRo K) (winRo_slots K) (S₁.ro hW hF).1) hone_lt) fun s₂ h₂ => ?_
  obtain ⟨sc₂, k₂, U₂, M₂, Dl, DJ, -, -⟩ := jacPost_frame hW S₁.scr S₁.mod (Or.inr (Or.inl rfl)) h₂
  have S₂ := S₁.next hW sc₂ (k₂.mono clob_nafClob) U₂
  refine WP.mono (setCounter_ok s₂ (j := 64 * K.M.n) (by omega)) fun s₃ ⟨x₃, k₃⟩ => ?_
  have S₃ := S₂.regs hW k₃ (fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)) (by decide)
  have t₃ : ∀ x, tmv C K.M.n base s₃ x = tmv C K.M.n base s₂ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₃.mem]
  have Dl₃ : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₃.mem base x K.M.n < C.p := by
    rw [k₃.mem]; exact Dl
  have hz : Naf5.residual k (64 * K.M.n + 1) = 0 := Naf5.residual_zero_top hk
  have DJ₃ : InvJ C (tmv C K.M.n base s₃ K.D.x) (tmv C K.M.n base s₃ K.D.y)
      (tmv C K.M.n base s₃ K.D.z) (mul (2 * Naf5.residual k (64 * K.M.n + 1)) P) := by
    rw [t₃, t₃, t₃, hz, Nat.mul_zero, show mul 0 P = .infinity by rw [Spec.Weierstrass.mul]; simp]
    exact DJ
  exact ⟨S₃, CacheUpTo.ofMem k₃.mem (CacheOk.unch hW hL.cache hc U₂ S₁.scr.nowrap), x₃, Dl₃, DJ₃⟩

/-- `[k]P` into `R`, projective, for `k < 2^(64 n)` whose digits are at `K.bits`. -/
theorem window_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) (hO : PrimeOrder C)
    (hn17 : 17 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) (hF : NafFixed K C base s P k)
    (hz1 : tmv C K.M.n base s K.P.z = 1) (hk : k < 2 ^ (64 * K.M.n)) {dd : Option (Prog isa)}
    (hD : NafDblOk K C base size dd) :
    WP isa (PubNaf.window K dd) s fun t => Scr t base size ∧ KeepRegs (nafClob K.M.n) s t ∧
      Unch base (winW K ++ cacheW K) s.mem t.mem ∧ ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal t.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y) (tmv C K.M.n base t K.R.z)
        (mul k P) := by
  have hW := hL.win
  have hn0 := hW.n0
  have h6 := hL.n6
  have hn := hs.nowrap
  rw [PubNaf.window]
  refine WP.seq (WP.mono (table_ok hL hp hC hM3 hO hn17 hP hs hM hF hz1) fun s₁ S₁ => ?_)
  -- The cache, from which the loop goes on.
  refine WP.seq (WP.mono (cacheTo_ok hL hp S₁.scr S₁.mod S₁.tbl 8 (Nat.le_refl _))
    fun s₂ ⟨sc₂, k₂, U₂, M₂, T₂, C₂⟩ => ?_)
  have U₀₂ : Unch base (winW K ++ cacheW K) s.mem s₂.mem := (S₁.unch.trans U₂).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢
    rcases hw with hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr hw
    · exact Or.inl (loopW_sub K w hw)
  have F₂ := hF.rebase hL U₀₂ hn
  have S₂ : NSt K C base size P s₂ s₂ := ⟨sc₂, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, M₂, T₂⟩
  -- `D = O`, `x19 = 64 n`.
  apply WP.seq
  refine WP.mono (head_ok hL hone_lt F₂ S₂ C₂ hk) fun s₃ ⟨S₃, C₃, x₃, Dl₃, DJ₃⟩ => ?_
  apply WP.seq
  refine WP.mono (digit_ok hL hp hC hM3 hone_lt hP S₃ F₂ C₃ (j := 64 * K.M.n) (by omega) x₃ Dl₃ DJ₃)
    fun s₄ I₄ => ?_
  apply WP.seq
  refine countLoop_ok (Inv := fun j t => NInv K C base size P s₂ t j (Naf5.residual k j))
    (n := 64 * K.M.n) (by omega) (fun j t hj1 hjn hI => ?_) (fun t hI => ?_) (by omega) I₄
  · have e : j - 1 + 1 = j := by omega
    refine WP.mono (stepOf_ok hL hp hC hM3 hone_lt hP F₂ hD (j := j - 1) (by omega) (by rw [e]; exact hI))
      fun t' h' => ⟨h', h'.x19⟩
  · refine WP.mono (finish_ok hL hp hC hpn hone_lt hone F₂ hI.st hI.rlt hI.r) fun t' ⟨S', l', r'⟩ => ?_
    refine ⟨S'.scr, S₁.keep.trans (k₂.trans S'.keep), (U₀₂.trans S'.unch).mono fun w hw => ?_, S'.mod, l',
      by rw [Naf5.residual_zero] at r'; exact r'⟩
    simp only [List.mem_append] at hw ⊢
    rcases hw with hw | hw
    · exact hw
    · exact Or.inl hw

end VG.Proof.Weierstrass.AArch64.PubNaf
