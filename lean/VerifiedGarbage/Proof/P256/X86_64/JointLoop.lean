import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublic
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler

/-! P-256's in-place doubler is a doubler of the shared two-scalar loop. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem p256_doubler {c : Joint.Cfg} {size : Nat}
    (hL : JointLayout c size) (hn : c.K.M.n=4) (hm : UnitMod Spec.P256.p (2^(64*c.K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve)
    (hd : (doubleSlots c.K.S c.K.R).Nodup) (hct : ScratchCT (jointDouble c.K)) :
    JointDoubler c Spec.P256.curve size (jointDouble c.K) := by
  have hw : ∀ x∈doubleSlots c.K.S c.K.R,x∈jointWork c := by
    intro x hx
    simp only [doubleSlots,jointWork,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hs : ∀ x∈doubleSlots c.K.S c.K.R,x∈jointSlots c := by
    intro x hx
    have h := hw x hx
    simp only [jointWork,jointSlots,nafSlots,List.mem_append] at h ⊢
    grind
  constructor
  · intro base u v Q A External s hExt hA h
    refine WP.mono_syms (doubleHalfPublic_ok hn hL.lay hm hC ha hd hs h.field (jointLive_R c) hA h.point)
      fun t ⟨kt,it,pt⟩ st => ?_
    have kw := kt.mono hw
    exact ⟨kw,h.next hL kw (it.sub (fun _ hx => List.mem_append_right _ hx)) pt (hExt s t kw st h.external)⟩
  · intro base E
    exact (doubleHalfPublic_relCT hn hL.lay hm hs (jointLive_R c) hct).mono (fun _ _ h => h)
      (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_append_right _ hx)⟩)

theorem joint_double_nodup : (doubleSlots publicJoint.K.S publicJoint.K.R).Nodup := by decide

theorem joint_adx_double_nodup : (doubleSlots publicJointAdx.K.S publicJointAdx.K.R).Nodup := by decide

end VG.Proof.P256.X86_64
