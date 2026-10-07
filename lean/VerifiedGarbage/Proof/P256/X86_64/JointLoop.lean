import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublic
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoop

/-! P-256's in-place doubler supplies the complete shared two-scalar loop. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem jointDouble_core_ok {c : Joint.Cfg} {base T : Addr} {size u v : Nat}
    {G Q A : Point Spec.P256.curve} {row : JointGeneratorRow Spec.P256.curve G} {s : State}
    (hL : JointLayout c size) (hm : UnitMod Spec.P256.p (2^(64*c.K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve)
    (hd : (doubleSlots c.K.S c.K.R).Nodup) (hA : onCurve Spec.P256.curve A=true)
    (h : JointCore c Spec.P256.curve base size Q u v
      (JointGenerator c Spec.P256.curve base T size row) A s) :
    WP isa (doubleHalfPublic c.K.M c.K.S c.K.R) s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c Spec.P256.curve base size Q u v
        (JointGenerator c Spec.P256.curve base T size row) (add A A) t := by
  have hw : ∀ x∈doubleSlots c.K.S c.K.R,x∈jointWork c := by
    intro x hx
    simp only [doubleSlots,jointWork,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hs : ∀ x∈doubleSlots c.K.S c.K.R,x∈jointSlots c := by
    intro x hx
    have h := hw x hx
    simp only [jointWork,jointSlots,nafSlots,List.mem_append] at h ⊢
    grind
  refine WP.mono_syms (doubleHalfPublic_ok hL.n hL.lay hm hC ha hd hs h.field (jointLive_R c) hA h.point)
    fun t ⟨kt,it,pt⟩ st => ?_
  have kw := kt.mono hw
  exact ⟨kw,h.next hL kw (it.sub (fun _ hx => List.mem_append_right _ hx)) pt
    (JointGenerator.workKeep hL h.field.mod.tmp s t kw st h.external)⟩

theorem p256_jointRun_ok {c : Joint.Cfg} {base T : Addr} {size u v : Nat}
    {G Q : Point Spec.P256.curve} {row : JointGeneratorRow Spec.P256.curve G} {s : State}
    (hL : JointAddLayout c size) (hm : UnitMod Spec.P256.p (2^(64*c.K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve)
    (hd : (doubleSlots c.K.S c.K.R).Nodup)
    (hOne : c.K.one<Spec.P256.p) (hOneVal : toM Spec.P256.p (2^256) c.K.one=1)
    (hG : onCurve Spec.P256.curve G=true) (hQ : onCurve Spec.P256.curve Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (h : JointCore c Spec.P256.curve base size Q u v
      (JointGenerator c Spec.P256.curve base T size row) .infinity s) (hb : s.gpr .rbx=256) :
    WP isa (Joint.run c (doubleHalfPublic c.K.M c.K.S c.K.R)) s fun t =>
      JointLoopKeep c.K.M base (jointWork c) s t ∧
      JointCore c Spec.P256.curve base size Q u v
        (JointGenerator c Spec.P256.curve base T size row) (add (mul u G) (mul v Q)) t ∧
      t.gpr .rbx=0 :=
  jointRun_core_ok hL hm hC ha hOne hOneVal hG hQ
    (fun _ _ hp hi => jointDouble_core_ok hL.lookup.layout hm hC ha hd hp hi) hu hv h hb

theorem joint_double_nodup : (doubleSlots publicJoint.K.S publicJoint.K.R).Nodup := by decide

theorem joint_adx_double_nodup : (doubleSlots publicJointAdx.K.S publicJointAdx.K.R).Nodup := by decide

end VG.Proof.P256.X86_64
