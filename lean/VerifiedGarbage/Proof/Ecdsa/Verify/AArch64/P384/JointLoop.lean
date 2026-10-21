module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDoubleD
public import VerifiedGarbage.Proof.Weierstrass.Joint
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.Chain
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit
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
