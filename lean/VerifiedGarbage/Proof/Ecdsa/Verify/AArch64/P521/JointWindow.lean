module

public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDouble
public import VerifiedGarbage.Proof.Weierstrass.Joint
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P521Joint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit

/-! ### `Ecdsa.Verify.AArch64.P521.JointLoop`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

/-- Fixed-generator arithmetic is independent of the joint loop's group recurrence. -/
def FixedStep (C : Curve) (base : Addr) (P G : Point C) (s₀ : State) (u : Nat) : Prop :=
 ∀(s : State) (j : Nat) (A : Point C),j<577 → onCurve C A=true →
  s.syms=s₀.syms → JointDigitPost P521Joint.K C base 8192 P s₀ s j A →
  WP isa P521Joint.fixedDigit s fun t=>
   JointDigitPost P521Joint.K C base 8192 P s₀ t j (add A (FastNaf.point C G 7 u j))

theorem digits_ok {C : Curve} {base : Addr} {P G A : Point C} {s₀ s : State} {u v j : Nat}
 (hL : NafLay P521Joint.K 8192) (hp : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P521Joint.K.one<C.p) (hP : onCurve C P=true)
 (hA : onCurve C A=true) (hF : NafFixed P521Joint.K C base s₀ P v)
 (fixed : FixedStep C base P G s₀ u) (hj : j<577) (sym : s.syms=s₀.syms)
 (h : JointDoublePost P521Joint.K C base 8192 P s₀ s j A) :
 WP isa P521Joint.digits s fun t=>
  JointDigitPost P521Joint.K C base 8192 P s₀ t j
   (add (add A (FastNaf.point C P 5 v j)) (FastNaf.point C G 7 u j)) := by
 rw [P521Joint.digits]
 refine WP.seq (WP.mono_syms (jointDigit_ok hL hp hC hM3 hone hP hA h.st hF h.cache hj h.x19 h.dlt h.d)
  fun a ha sy=>?_) 
 exact fixed a j _ hj (hC.onCurve_add hA (Naf5.onCurve_point hC hP v j)) (sy.trans sym) ha

theorem step_ok {C : Curve} {base : Addr} {P G : Point C} {s₀ s : State} {u v j : Nat}
 (hL : NafLay P521Joint.K 8192) (hp : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P521Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hF : NafFixed P521Joint.K C base s₀ P v) (fixed : FixedStep C base P G s₀ u)
 (hj : j<576) (sym : s.syms=s₀.syms)
 (h : JointDigitPost P521Joint.K C base 8192 P s₀ s (j+1) (jointPoint G P u v (j+1))) :
 WP isa P521Joint.step s fun t=>
  JointDigitPost P521Joint.K C base 8192 P s₀ t j (jointPoint G P u v j) := by
 rw [P521Joint.step]
 apply WP.assoc
 refine WP.seq (WP.mono_syms (jointDouble_ok hL hp hC hM3 hF
  (jointPoint_curve hC hG hP u v (j+1)) (by change j<577; omega_using [hj]) h) fun a ha sy=>?_) 
 refine WP.mono (digits_ok hL hp hC hM3 hone hP
  (hC.onCurve_add (jointPoint_curve hC hG hP u v (j+1)) (jointPoint_curve hC hG hP u v (j+1)))
  hF fixed (by omega_using [hj]) (sy.trans sym) ha) fun t ht=>?_
 rw [jointPoint_step hC hG hP] at ht
 exact ht

/-- The original public NAF iteration also works on a joint accumulator. -/
theorem peerStep_ok {C : Curve} {base : Addr} {P A : Point C} {s₀ s : State} {v j : Nat}
 (hL : NafLay P521Joint.K 8192) (hp : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P521Joint.K.one<C.p) (hP : onCurve C P=true) (hA : onCurve C A=true)
 (hF : NafFixed P521Joint.K C base s₀ P v) (hj : j<576)
 (h : JointDigitPost P521Joint.K C base 8192 P s₀ s (j+1) A) :
 WP isa (PubNaf.step P521Joint.K) s fun t=>
  JointDigitPost P521Joint.K C base 8192 P s₀ t j (add (add A A) (Naf5.point C P v j)) := by
 rw [PubNaf.step]
 apply WP.assoc
 refine WP.seq (WP.mono (jointDouble_ok hL hp hC hM3 hF hA (by change j<577; omega_using [hj]) h) fun a ha=>?_)
 exact jointDigit_ok hL hp hC hM3 hone hP (hC.onCurve_add hA hA) ha.st hF ha.cache
  (by change j<577; omega_using [hj]) ha.x19 ha.dlt ha.d

theorem loop_ok {C : Curve} {base : Addr} {P G : Point C} {s₀ s : State} {u v : Nat}
 (hL : NafLay P521Joint.K 8192) (hp : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P521Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hF : NafFixed P521Joint.K C base s₀ P v) (fixed : FixedStep C base P G s₀ u)
 (sym : s.syms=s₀.syms)
 (h : JointDigitPost P521Joint.K C base 8192 P s₀ s 576 (jointPoint G P u v 576)) :
 WP isa (.loop P521Joint.step (.nonzero .x .x19)) s fun t=>
  JointDigitPost P521Joint.K C base 8192 P s₀ t 0 (add (mul u G) (mul v P)) ∧ t.syms=s₀.syms := by
 let I := fun j t=>JointDigitPost P521Joint.K C base 8192 P s₀ t j (jointPoint G P u v j) ∧ t.syms=s₀.syms
 apply countLoop_ok (Inv:=I) (n:=576) (by decide)
 · intro j a hj0 hjn hi
   have e : j-1+1=j := by omega_using [hj0]
   refine WP.mono_syms (step_ok (j:=j-1) hL hp hC hM3 hone hP hG hF fixed (by omega_using [hjn]) hi.2
    (by rw [e]; exact hi.1)) fun t ht sy=>?_
   exact ⟨⟨ht,sy.trans hi.2⟩,ht.x19⟩
 · intro t ht
   dsimp only [I] at ht
   rw [jointPoint_zero] at ht
   exact ht
 · decide
 · exact ⟨h,sym⟩
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint

end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass
theorem window_ok {C : Curve} {base : Addr} {u v : Nat} (hL : NafLay P521Joint.K 8192)
    (hp : UnitMod C.p (2 ^ (64 * P521Joint.K.M.n))) (hC : Law C) (hM3 : AM3 C) (hpn : C.p < 2 ^ (64 * P521Joint.K.M.n))
    (hone_lt : P521Joint.K.one < C.p) (hone : toM C.p (2 ^ (64 * P521Joint.K.M.n)) P521Joint.K.one = 1) (hO : PrimeOrder C)
    (hn17 : 17 ≤ C.n) {P G : Point C} (hP : onCurve C P = true) (hG : onCurve C G=true) {s : State} (hs : Scr s base 8192)
    (hM : ModOkA P521Joint.K.M 8192 C.p s.mem base) (hF : NafFixed P521Joint.K C base s P v)
    (hz1 : tmv C P521Joint.K.M.n base s P521Joint.K.P.z = 1) (hv : v < 2 ^ (64 * P521Joint.K.M.n)) (hu : u < 2^(64*P521Joint.K.M.n))
    (fixed : ∀t, Unch base (winW P521Joint.K ++ cacheW P521Joint.K) s.mem t.mem → t.rd=s.rd → t.wr=s.wr → t.syms=s.syms → FixedStep C base P G t u) :
    WP isa P521Joint.window s fun t => Scr t base 8192 ∧ KeepRegs (nafClob P521Joint.K.M.n) s t ∧
      Unch base (winW P521Joint.K ++ cacheW P521Joint.K) s.mem t.mem ∧ ModOkA P521Joint.K.M 8192 C.p t.mem base ∧
      (∀ x ∈ [P521Joint.K.R.x, P521Joint.K.R.y, P521Joint.K.R.z], wordsVal t.mem base x P521Joint.K.M.n < C.p) ∧
      Rep C (tmv C P521Joint.K.M.n base t P521Joint.K.R.x) (tmv C P521Joint.K.M.n base t P521Joint.K.R.y) (tmv C P521Joint.K.M.n base t P521Joint.K.R.z)
        (add (mul u G) (mul v P)) := by
  have hn := hs.nowrap
  rw [P521Joint.window]
  refine WP.seq (WP.mono_syms (table_ok hL hp hC hM3 hO hn17 hP hs hM hF hz1) fun s₁ S₁ sy₁ => ?_)
  -- The cache, from which the loop goes on.
  refine WP.seq (WP.mono_syms (cacheTo_ok hL hp S₁.scr S₁.mod S₁.tbl 8 (Nat.le_refl _))
    fun s₂ ⟨sc₂, k₂, U₂, M₂, T₂, C₂⟩ sy₂ => ?_)
  have U₀₂ : Unch base (winW P521Joint.K ++ cacheW P521Joint.K) s.mem s₂.mem := (S₁.unch.trans U₂).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢
    rcases hw with hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr hw
    · exact Or.inl (loopW_sub P521Joint.K w hw)
  have F₂ := hF.rebase hL U₀₂ hn
  have S₂ : NSt P521Joint.K C base 8192 P s₂ s₂ := ⟨sc₂, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, M₂, T₂⟩
  have fixed₂ := fixed s₂ U₀₂ (k₂.rd.trans S₁.keep.rd) (k₂.wr.trans S₁.keep.wr) (sy₂.trans sy₁)
  apply WP.seq
  refine WP.mono_syms (head_ok hL hone_lt F₂ S₂ C₂ hv) fun s₃ ⟨S₃,C₃,x₃,Dl₃,DJ₃⟩ sy₃ => ?_
  have top := jointPoint_topB (B:=64*P521Joint.K.M.n) (u:=u) (v:=v) G P hu hv
  change jointPoint G P u v 577 = .infinity at top
  have dj : InvJ C (tmv C P521Joint.K.M.n base s₃ P521Joint.K.D.x)
    (tmv C P521Joint.K.M.n base s₃ P521Joint.K.D.y) (tmv C P521Joint.K.M.n base s₃ P521Joint.K.D.z)
    (add (jointPoint G P u v 577) (jointPoint G P u v 577)) := by
    rw [top]
    have hz := Naf5.residual_zero_top hv
    change Naf5.residual v 577=0 at hz
    change InvJ C _ _ _ (mul (2*Naf5.residual v 577) P) at DJ₃
    rw [hz,Nat.mul_zero,Spec.Weierstrass.mul] at DJ₃
    exact DJ₃
  apply WP.seq
  refine WP.mono_syms (digits_ok hL hp hC hM3 hone_lt hP
    (hC.onCurve_add (jointPoint_curve hC hG hP u v 577) (jointPoint_curve hC hG hP u v 577))
    F₂ fixed₂ (j:=576) (by decide) sy₃ ⟨S₃,x₃,Dl₃,dj,C₃⟩) fun s₄ I₄ sy₄ => ?_
  rw [jointPoint_step hC hG hP] at I₄
  apply WP.seq
  refine WP.mono (loop_ok hL hp hC hM3 hone_lt hP hG F₂ fixed₂ (sy₄.trans sy₃) I₄) fun s₅ ⟨I₅,_⟩=>?_
  refine WP.mono (jointFinish_ok hL hp hC hpn hone_lt hone F₂ I₅.st I₅.rlt I₅.r) fun t ⟨S',l',r'⟩=>?_
  refine ⟨S'.scr,S₁.keep.trans (k₂.trans S'.keep),(U₀₂.trans S'.unch).mono fun w hw=>?_,S'.mod,l',r'⟩
  simp only [List.mem_append] at hw ⊢
  rcases hw with hw | hw
  · exact hw
  · exact Or.inl hw
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
