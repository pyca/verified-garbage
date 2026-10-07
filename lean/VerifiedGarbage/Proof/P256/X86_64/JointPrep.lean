import VerifiedGarbage.Proof.P256.X86_64.JointWindowTiming
import VerifiedGarbage.Proof.P256.X86_64.FastNafTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepFields

/-! Connect the two scalar recoders to the verified joint-window input. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem joint_prep_layout : JointPrepLayout publicJoint 8192
    (Impl.Ecdsa.X86_64.p256.sl Impl.Ecdsa.Verify.X86_64.U)
    (Impl.Ecdsa.X86_64.p256.sl Impl.Ecdsa.Verify.X86_64.V) := by
  constructor <;> decide

theorem joint_adx_prep_layout : JointPrepLayout publicJointAdx 8192
    (Impl.Ecdsa.X86_64.p256x.sl Impl.Ecdsa.Verify.X86_64.U)
    (Impl.Ecdsa.X86_64.p256x.sl Impl.Ecdsa.Verify.X86_64.V) := by
  constructor <;> decide

theorem p256_jointPrepInput_ok {c : Joint.Cfg} {base T : Addr} {size srcU srcV u v : Nat}
    {G Q : Point Spec.P256.curve} {row : JointGeneratorRow Spec.P256.curve G}
    {E : Nat → Fin Spec.P256.p} {s : State}
    (hL : JointPrepLayout c size srcU srcV) (hF : Lay c.K.M size (·∈nafSlots c.K))
    (hi : Inv c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K) E s)
    (hp : InvJ Spec.P256.curve (E c.K.P.x) (E c.K.P.y) (E c.K.P.z) Q)
    (hz : E c.K.zero=0) (he : JointGenerator c Spec.P256.curve base T size row s)
    (hu : wordsVal s.mem base srcU 4=u) (hv : wordsVal s.mem base srcV 4=v) :
    WP isa (Joint.prep c srcU srcV) s fun t =>
      Inv c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K) E t ∧
      JointWindowInput c base T size u v Q row t ∧ KeepRegs nafPrepClob s t ∧
      Unch base (jointPrepRanges c) s.mem t.mem := by
  refine WP.mono (jointPrepFields_ok (C:=Spec.P256.curve) hL hF hi he)
    fun t ⟨it,dg,dq,gt,hk,ht⟩ => ?_
  rw [hu] at dg
  rw [hv] at dq
  have pv : ∀ x∈jacCoords c.K.P,x∈winRo c.K := by
    intro x hx
    simp only [jacCoords,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  exact ⟨it,⟨it.point_tmv pv hp,(it.val _ (by simp [winRo])).trans hz,dq,dg,gt⟩,hk,ht⟩

theorem p256_jointPrepInput_relCT {c : Joint.Cfg} {base T : Addr} {size srcU srcV u v : Nat}
    {G Q : Point Spec.P256.curve} {row : JointGeneratorRow Spec.P256.curve G} {E : Nat → Fin Spec.P256.p}
    (hL : JointPrepLayout c size srcU srcV) (hF : Lay c.K.M size (·∈nafSlots c.K))
    (hp : InvJ Spec.P256.curve (E c.K.P.x) (E c.K.P.y) (E c.K.P.z) Q) (hz : E c.K.zero=0)
    (hcG : FastPrepChecks srcU c.gBits 7) (hcQ : FastPrepChecks srcV c.K.bits 5) :
    RelCT isa (fun s t => FieldPair c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointGenerator c Spec.P256.curve base T size row s ∧ JointGenerator c Spec.P256.curve base T size row t ∧
      wordsVal s.mem base srcU 4=u ∧ wordsVal s.mem base srcV 4=v ∧
      wordsVal t.mem base srcU 4=u ∧ wordsVal t.mem base srcV 4=v)
      (Joint.prep c srcU srcV)
      (fun s t => FieldPair c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
        JointWindowInput c base T size u v Q row s ∧ JointWindowInput c base T size u v Q row t) := by
  have ct := (jointPrep_relCT (base:=base) hL.sourceU hL.sourceV hL.generator hL.peer hL.keepV hcG hcQ).mono
    (P':=fun (s t : State) => FieldPair c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointGenerator c Spec.P256.curve base T size row s ∧ JointGenerator c Spec.P256.curve base T size row t ∧
      wordsVal s.mem base srcU 4=u ∧ wordsVal s.mem base srcV 4=v ∧
      wordsVal t.mem base srcU 4=u ∧ wordsVal t.mem base srcV 4=v)
    (fun _ _ ⟨p,_,_,su,sv,tu,tv⟩ => ⟨p.1.scr,p.2.scr,su.trans tu.symm,sv.trans tv.symm⟩)
    (fun _ _ h => h)
  let Post := fun (s : State) => Inv c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K) E s ∧
    JointWindowInput c base T size u v Q row s
  exact (ct.wp (F₁:=Post) (F₂:=Post) (fun s t ⟨p,gs,gt,su,sv,tu,tv⟩ =>
    ⟨WP.mono (p256_jointPrepInput_ok hL hF p.1 hp hz gs su sv) (fun _ h => ⟨h.1,h.2.1⟩),
     WP.mono (p256_jointPrepInput_ok hL hF p.2 hp hz gt tu tv) (fun _ h => ⟨h.1,h.2.1⟩)⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_,ps,pt⟩ => ⟨⟨ps.1,pt.1⟩,ps.2,pt.2⟩)

end VG.Proof.P256.X86_64
