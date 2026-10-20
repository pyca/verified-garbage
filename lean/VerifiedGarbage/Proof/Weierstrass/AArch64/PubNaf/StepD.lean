module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table

/-!
# The public NAF's iterations with a given doubling

`stepD_ok`: an iteration whose doubling is one that does what the field
program's does (`DblSpec`, such as P-384's register-allocated doubling), as
`step_ok` for the field program's; `stepOf_ok`, for either.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The doubling a window is given, if any, does what the field program's does. -/
def NafDblOk (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (dd : Option (Prog isa)) : Prop :=
  ∀ d, dd = some d → DblSpec K C base size d K.R K.D (dblVR K)

theorem NafDblOk.none {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} : NafDblOk K C base size none :=
  fun _ h => by cases h

/-- An iteration with the doubling `d`: `D = 2R`, then the digit. -/
theorem stepD_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hone : K.one < C.p)
    {P : Point C} (hP : onCurve C P = true) {s₀ s : State} (hF : NafFixed K C base s₀ P k)
    {d : Prog isa} (hd : DblSpec K C base size d K.R K.D (dblVR K)) {j : Nat}
    (hj : j < 64 * K.M.n + 1) (h : NInv K C base size P s₀ s (j + 1) (Naf5.residual k (j + 1))) :
    WP isa (PubNaf.stepD K d) s fun t => NInv K C base size P s₀ t j (Naf5.residual k j) := by
  have hW := hL.win
  rw [PubNaf.stepD]
  refine WP.seq (WP.mono (decCounter_ok s (by omega) (by have := hL.n6; omega) h.x19)
    fun s₁ ⟨x₁, k₁⟩ => ?_)
  have S₁ := h.st.regs hW k₁ (fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)) (by decide)
  have t₁ : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₁.mem]
  have V0 : ∀ x ∈ dblVR K, x ∈ winSlots K ∧ wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    simp only [dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (R_other K _ (by simp)), by rw [k₁.mem]; exact h.rlt _ (by simp)⟩
    · exact ⟨winOther_mem (R_other K _ (by simp)), by rw [k₁.mem]; exact h.rlt _ (by simp)⟩
    · exact ⟨winOther_mem (R_other K _ (by simp)), by rw [k₁.mem]; exact h.rlt _ (by simp)⟩
    all_goals exact ⟨winRo_slots K _ (by simp [winRo]), (S₁.ro hW hF).1 _ (by simp [winRo])⟩
  have I₁ : Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) (tmv C K.M.n base s₁) s₁ :=
    inv_of S₁.scr S₁.mod (fun x hx => (V0 x hx).1) (fun x hx => (V0 x hx).2)
  have RJ₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y) (tmv C K.M.n base s₁ K.R.z)
      (mul (Naf5.residual k (j + 1)) P) := by rw [t₁, t₁, t₁]; exact h.r
  refine WP.seq (WP.mono (hd _ s₁ I₁) fun s₂ ⟨k₂, U₂, E₂, I₂, v₂⟩ => ?_)
  have dJ := InvJ.dbl' hC hM3 (hC.onCurve_mul hP _) RJ₁ (v₂.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.add_mul_mul hP, show Naf5.residual k (j + 1) + Naf5.residual k (j + 1) =
    2 * Naf5.residual k (j + 1) by omega] at dJ
  have S₂ := S₁.next hW I₂.scr (k₂.mono fun _ h => List.mem_cons_of_mem _ (winSaved_combClob h)) U₂
  have x₂ : s₂.gpr .x19 = BitVec.ofNat 64 j := by
    have n19 : Reg.x19 ∉ clob K.M.n ++ winSaved K.M.n := fun h =>
      (List.mem_append.mp h).elim (x19_not_clob _) (not_mem_winSaved (by decide))
    rw [k₂.gpr _ n19, x₁, Nat.add_sub_cancel]
  have Dl : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₂.mem base x K.M.n < C.p :=
    fun x hx => I₂.lt x (List.mem_append_left _ hx)
  have DJ : InvJ C (tmv C K.M.n base s₂ K.D.x) (tmv C K.M.n base s₂ K.D.y) (tmv C K.M.n base s₂ K.D.z)
      (mul (2 * Naf5.residual k (j + 1)) P) := by
    rw [show tmv C K.M.n base s₂ K.D.x = E₂ K.D.x from I₂.val _ (by simp),
      show tmv C K.M.n base s₂ K.D.y = E₂ K.D.y from I₂.val _ (by simp),
      show tmv C K.M.n base s₂ K.D.z = E₂ K.D.z from I₂.val _ (by simp)]
    exact dJ
  exact digit_ok hL hp hC hM3 hone hP S₂ hF
    (CacheOk.unch hW hL.cache (CacheUpTo.ofMem k₁.mem h.cache) U₂ S₁.scr.nowrap) hj x₂ Dl DJ

/-- An iteration, with the doubling given, if any. -/
theorem stepOf_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hone : K.one < C.p)
    {P : Point C} (hP : onCurve C P = true) {s₀ s : State} (hF : NafFixed K C base s₀ P k)
    {dd : Option (Prog isa)} (hD : NafDblOk K C base size dd) {j : Nat}
    (hj : j < 64 * K.M.n + 1) (h : NInv K C base size P s₀ s (j + 1) (Naf5.residual k (j + 1))) :
    WP isa (PubNaf.stepOf K dd) s fun t => NInv K C base size P s₀ t j (Naf5.residual k j) := by
  cases dd with
  | none => exact step_ok hL hp hC hM3 hone hP hF hj h
  | some d => exact stepD_ok hL hp hC hM3 hone hP hF (hD d rfl) hj h

end VG.Proof.Weierstrass.AArch64.PubNaf
