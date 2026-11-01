module

public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDouble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.StepD
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract

-- Formerly `VerifiedGarbage/Proof/Weierstrass/AArch64/PubNaf/JointDoubleD.lean`, which only this module imported.
section

/-! # The joint loop's shared doubling, by a given doubling

`jointDoubleD_ok`: `jointDouble_ok` with a doubling that does what the field program's does
(`DblSpec`, such as P-384's register-allocated doubling). -/

section
namespace VG.Proof.Weierstrass.AArch64.PubNaf
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

theorem jointDoubleD_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hC : Law C) (hM3 : AM3 C)
    {P : Point C} {s₀ s : State} (hF : NafFixed K C base s₀ P k) {A : Point C} (hA : onCurve C A=true)
    {d : Prog isa} (hd : DblSpec K C base size d K.R K.D (dblVR K)) {j : Nat}
    (hj : j < 64 * K.M.n + 1) (h : JointDigitPost K C base size P s₀ s (j + 1) A) :
    WP isa (.seq (.block [decCounter]) d) s fun t =>
      JointDoublePost K C base size P s₀ t j (Spec.Weierstrass.add A A) := by
  have hW := hL.win
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
      A := by rw [t₁, t₁, t₁]; exact h.r
  refine WP.mono (hd _ s₁ I₁) fun s₂ ⟨k₂, U₂, E₂, I₂, v₂⟩ => ?_
  have dJ := InvJ.dbl' hC hM3 hA RJ₁ (v₂.trans (dblJChoiceN_run (K.M.n == 4) _))
  have S₂ := S₁.next hW I₂.scr (k₂.mono fun _ h => List.mem_cons_of_mem _ (winSaved_combClob h)) U₂
  have x₂ : s₂.gpr .x19 = BitVec.ofNat 64 j := by
    have n19 : Reg.x19 ∉ clob K.M.n ++ winSaved K.M.n := fun h =>
      (List.mem_append.mp h).elim (x19_not_clob _) (not_mem_winSaved (by decide))
    rw [k₂.gpr _ n19, x₁, Nat.add_sub_cancel]
  have Dl : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₂.mem base x K.M.n < C.p :=
    fun x hx => I₂.lt x (List.mem_append_left _ hx)
  have DJ : InvJ C (tmv C K.M.n base s₂ K.D.x) (tmv C K.M.n base s₂ K.D.y) (tmv C K.M.n base s₂ K.D.z)
      (Spec.Weierstrass.add A A) := by
    rw [show tmv C K.M.n base s₂ K.D.x = E₂ K.D.x from I₂.val _ (by simp),
      show tmv C K.M.n base s₂ K.D.y = E₂ K.D.y from I₂.val _ (by simp),
      show tmv C K.M.n base s₂ K.D.z = E₂ K.D.z from I₂.val _ (by simp)]
    exact dJ
  exact ⟨S₂, x₂, Dl, DJ, CacheOk.unch hW hL.cache (CacheUpTo.ofMem k₁.mem h.cache) U₂ S₁.scr.nowrap⟩

end VG.Proof.Weierstrass.AArch64.PubNaf
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

/-- Fixed-generator arithmetic is independent of the joint loop's group recurrence. -/
def FixedStep (C : Curve) (base : Addr) (P G : Point C) (s₀ : State) (u : Nat) : Prop :=
 ∀(s : State) (j : Nat) (A : Point C),j<385 → onCurve C A=true →
  s.syms=s₀.syms → JointDigitPost P384Joint.K C base 8192 P s₀ s j A →
  WP isa P384Joint.fixedDigit s fun t=>
   JointDigitPost P384Joint.K C base 8192 P s₀ t j (add A (FastNaf.point C G 9 u j))

theorem digits_ok {C : Curve} {base : Addr} {P G A : Point C} {s₀ s : State} {u v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true)
 (hA : onCurve C A=true) (hF : NafFixed P384Joint.K C base s₀ P v)
 (fixed : FixedStep C base P G s₀ u) (hj : j<385) (sym : s.syms=s₀.syms)
 (h : JointDoublePost P384Joint.K C base 8192 P s₀ s j A) :
 WP isa P384Joint.digits s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t j
   (add (add A (FastNaf.point C P 5 v j)) (FastNaf.point C G 9 u j)) := by
 rw [P384Joint.digits]
 refine WP.seq (WP.mono_syms (jointDigit_ok hL hp hC hM3 hone hP hA h.st hF h.cache hj h.x19 h.dlt h.d)
  fun a ha sy=>?_) 
 exact fixed a j _ hj (hC.onCurve_add hA (Naf5.onCurve_point hC hP v j)) (sy.trans sym) ha

theorem step_ok {C : Curve} {base : Addr} {P G : Point C} {s₀ s : State} {u v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hF : NafFixed P384Joint.K C base s₀ P v) (fixed : FixedStep C base P G s₀ u)
 (hj : j<384) (sym : s.syms=s₀.syms)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s (j+1) (jointPoint G P u v (j+1) 9)) :
 WP isa P384Joint.step s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t j (jointPoint G P u v j 9) := by
 rw [P384Joint.step]
 apply WP.assoc
 refine WP.seq (WP.mono_syms (jointDoubleD_ok hL hC hM3 hF
  (jointPoint_curve hC hG hP u v (j+1) 9) hD (by change j<385; omega) h) fun a ha sy=>?_)
 refine WP.mono (digits_ok hL hp hC hM3 hone hP
  (hC.onCurve_add (jointPoint_curve hC hG hP u v (j+1) 9) (jointPoint_curve hC hG hP u v (j+1) 9))
  hF fixed (by omega) (sy.trans sym) ha) fun t ht=>?_
 rw [jointPoint_step hC hG hP u v j 9] at ht
 exact ht

/-- The public NAF's iteration with the allocated doubling also works on a joint accumulator. -/
theorem peerStepD_ok {C : Curve} {base : Addr} {P A : Point C} {s₀ s : State} {v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hA : onCurve C A=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hF : NafFixed P384Joint.K C base s₀ P v) (hj : j<384)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s (j+1) A) :
 WP isa (PubNaf.stepD P384Joint.K P384Joint.double) s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t j (add (add A A) (Naf5.point C P v j)) := by
 rw [PubNaf.stepD]
 apply WP.assoc
 refine WP.seq (WP.mono (jointDoubleD_ok hL hC hM3 hF hA hD (by change j<385; omega) h) fun a ha=>?_)
 exact jointDigit_ok hL hp hC hM3 hone hP (hC.onCurve_add hA hA) ha.st hF ha.cache
  (by change j<385; omega) ha.x19 ha.dlt ha.d

theorem loop_ok {C : Curve} {base : Addr} {P G : Point C} {s₀ s : State} {u v : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hF : NafFixed P384Joint.K C base s₀ P v) (fixed : FixedStep C base P G s₀ u)
 (sym : s.syms=s₀.syms)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s 384 (jointPoint G P u v 384 9)) :
 WP isa (.loop P384Joint.step (.nonzero .x .x19)) s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t 0 (add (mul u G) (mul v P)) ∧ t.syms=s₀.syms := by
 let I := fun j t=>JointDigitPost P384Joint.K C base 8192 P s₀ t j (jointPoint G P u v j 9) ∧ t.syms=s₀.syms
 apply countLoop_ok (Inv:=I) (n:=384) (by decide)
 · intro j a hj0 hjn hi
   have e : j-1+1=j := by omega
   refine WP.mono_syms (step_ok (j:=j-1) hL hp hC hM3 hone hP hG hD hF fixed (by omega) hi.2
    (by rw [e]; exact hi.1)) fun t ht sy=>?_
   exact ⟨⟨ht,sy.trans hi.2⟩,ht.x19⟩
 · intro t ht
   dsimp only [I] at ht
   rw [jointPoint_zero G P u v 9] at ht
   exact ht
 · decide
 · exact ⟨h,sym⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
