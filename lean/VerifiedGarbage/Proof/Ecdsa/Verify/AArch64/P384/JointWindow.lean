module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointLoop
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Framework.AArch64.Syms
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass
theorem window_ok {C : Curve} {base : Addr} {u v : Nat} (hL : NafLay P384Joint.K 8192)
    (hp : UnitMod C.p (2 ^ (64 * P384Joint.K.M.n))) (hC : Law C) (hM3 : AM3 C) (hpn : C.p < 2 ^ (64 * P384Joint.K.M.n))
    (hone_lt : P384Joint.K.one < C.p) (hone : toM C.p (2 ^ (64 * P384Joint.K.M.n)) P384Joint.K.one = 1) (hO : PrimeOrder C)
    (hn17 : 17 ≤ C.n) {P G : Point C} (hP : onCurve C P = true) (hG : onCurve C G=true) {s : State} (hs : Scr s base 8192)
    (hM : ModOkA P384Joint.K.M 8192 C.p s.mem base) (hF : NafFixed P384Joint.K C base s P v)
    (hz1 : tmv C P384Joint.K.M.n base s P384Joint.K.P.z = 1) (hv : v < 2 ^ (64 * P384Joint.K.M.n)) (hu : u < 2^(64*P384Joint.K.M.n))
    (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
    (fixed : ∀t, Unch base (winW P384Joint.K ++ cacheW P384Joint.K) s.mem t.mem → t.rd=s.rd → t.wr=s.wr → t.syms=s.syms → FixedStep C base P G t u) :
    WP isa P384Joint.window s fun t => Scr t base 8192 ∧ KeepRegs (nafClob P384Joint.K.M.n) s t ∧
      Unch base (winW P384Joint.K ++ cacheW P384Joint.K) s.mem t.mem ∧ ModOkA P384Joint.K.M 8192 C.p t.mem base ∧
      (∀ x ∈ [P384Joint.K.R.x, P384Joint.K.R.y, P384Joint.K.R.z], wordsVal t.mem base x P384Joint.K.M.n < C.p) ∧
      Rep C (tmv C P384Joint.K.M.n base t P384Joint.K.R.x) (tmv C P384Joint.K.M.n base t P384Joint.K.R.y) (tmv C P384Joint.K.M.n base t P384Joint.K.R.z)
        (add (mul u G) (mul v P)) := by
  have hn := hs.nowrap
  rw [P384Joint.window]
  refine WP.seq (WP.mono_syms (table_ok hL hp hC hM3 hO hn17 hP hs hM hF hz1) fun s₁ S₁ sy₁ => ?_)
  -- The cache, from which the loop goes on.
  refine WP.seq (WP.mono_syms (cacheTo_ok hL hp S₁.scr S₁.mod S₁.tbl 8 (Nat.le_refl _))
    fun s₂ ⟨sc₂, k₂, U₂, M₂, T₂, C₂⟩ sy₂ => ?_)
  have U₀₂ : Unch base (winW P384Joint.K ++ cacheW P384Joint.K) s.mem s₂.mem := (S₁.unch.trans U₂).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢
    rcases hw with hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr hw
    · exact Or.inl (loopW_sub P384Joint.K w hw)
  have F₂ := hF.rebase hL U₀₂ hn
  have S₂ : NSt P384Joint.K C base 8192 P s₂ s₂ := ⟨sc₂, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, M₂, T₂⟩
  have fixed₂ := fixed s₂ U₀₂ (k₂.rd.trans S₁.keep.rd) (k₂.wr.trans S₁.keep.wr) (sy₂.trans sy₁)
  apply WP.seq
  refine WP.mono_syms (head_ok hL hone_lt F₂ S₂ C₂ hv) fun s₃ ⟨S₃,C₃,x₃,Dl₃,DJ₃⟩ sy₃ => ?_
  have top := jointPoint_topB (B:=64*P384Joint.K.M.n) (u:=u) (v:=v) G P hu hv 9
  change jointPoint G P u v 385 9 = .infinity at top
  have dj : InvJ C (tmv C P384Joint.K.M.n base s₃ P384Joint.K.D.x)
    (tmv C P384Joint.K.M.n base s₃ P384Joint.K.D.y) (tmv C P384Joint.K.M.n base s₃ P384Joint.K.D.z)
    (add (jointPoint G P u v 385 9) (jointPoint G P u v 385 9)) := by
    rw [top]
    have hz := Naf5.residual_zero_top hv
    change Naf5.residual v 385=0 at hz
    change InvJ C _ _ _ (mul (2*Naf5.residual v 385) P) at DJ₃
    rw [hz,Nat.mul_zero,Spec.Weierstrass.mul] at DJ₃
    exact DJ₃
  apply WP.seq
  refine WP.mono_syms (digits_ok hL hp hC hM3 hone_lt hP
    (hC.onCurve_add (jointPoint_curve hC hG hP u v 385 9) (jointPoint_curve hC hG hP u v 385 9))
    F₂ fixed₂ (j:=384) (by decide) sy₃ ⟨S₃,x₃,Dl₃,dj,C₃⟩) fun s₄ I₄ sy₄ => ?_
  rw [jointPoint_step hC hG hP u v 384 9] at I₄
  apply WP.seq
  refine WP.mono (loop_ok hL hp hC hM3 hone_lt hP hG hD F₂ fixed₂ (sy₄.trans sy₃) I₄) fun s₅ ⟨I₅,_⟩=>?_
  refine WP.mono (jointFinish_ok hL hp hC hpn hone_lt hone F₂ I₅.st I₅.rlt I₅.r) fun t ⟨S',l',r'⟩=>?_
  refine ⟨S'.scr,S₁.keep.trans (k₂.trans S'.keep),(U₀₂.trans S'.unch).mono fun w hw=>?_,S'.mod,l',r'⟩
  simp only [List.mem_append] at hw ⊢
  rcases hw with hw | hw
  · exact hw
  · exact Or.inl hw
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
