import VerifiedGarbage.Proof.P256.X86_64.JointLoop
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublicTiming
import VerifiedGarbage.Proof.P256.X86_64.JointFixedTiming
import VerifiedGarbage.Proof.P256.X86_64.NafCacheTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPairedTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming

/-! P-256's actual baseline and ADX operations instantiate the paired joint loop. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem joint_cached_checks : JointCachedChecks publicJoint := by
  refine ⟨?_,nafSignedCachedEntry_ct,nafCachedJac_checks,?_⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_cached_checks : JointCachedChecks publicJointAdx := by
  refine ⟨?_,nafSignedCachedEntry_adx_ct,nafCachedJac_adx_checks,?_⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_fixed_checks : JointFixedChecks publicJoint := by
  refine ⟨?_,jointFixedEntry_ct,nafMixedJac_checks,joint_cached_checks.copy⟩
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_fixed_checks : JointFixedChecks publicJointAdx := by
  refine ⟨?_,jointFixedEntry_adx_ct,nafMixedJac_adx_checks,joint_adx_cached_checks.copy⟩
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem p256_jointOpsTiming {c : Joint.Cfg} {base T : Addr} {size u v : Nat}
    {G Q : Point Spec.P256.curve} {row : JointGeneratorRow Spec.P256.curve G}
    (hL : JointAddLayout c size) (hm : UnitMod Spec.P256.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<Spec.P256.p) (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (hd : ScratchCT (doubleHalfPublic c.K.M c.K.S c.K.R)) :
    JointOpsTiming c (doubleHalfPublic c.K.M c.K.S c.K.R) Spec.P256.curve base size
      (JointCore c Spec.P256.curve base size Q u v (JointGenerator c Spec.P256.curve base T size row)) := by
  constructor
  · intro A j E
    have sl : ∀ x∈doubleSlots c.K.S c.K.R,x∈jointSlots c := by
      intro x hx
      simp only [doubleSlots,jointSlots,nafSlots,winOther,rcbW,List.mem_append,
        List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
    exact (doubleHalfPublic_relCT hL.lookup.layout.n hL.lookup.layout.lay hm sl (jointLive_R c) hd).mono
      (fun _ _ h => h.1) (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_append_right _ hx)⟩)
  · intro A j hj E
    exact jointCachedDigit_relCT hL hm hOne hj hc
      (fun _ _ hk st hs a ha hb ho => (hs a ha hb ho).of_keeps hk st)
  · intro A j hj E
    exact jointFixedDigit_relCT hL hm hOne hj hf

theorem p256_jointRun_relCT {c : Joint.Cfg} {base T : Addr} {size u v : Nat}
    {G Q : Point Spec.P256.curve} {row : JointGeneratorRow Spec.P256.curve G}
    (hL : JointAddLayout c size) (hm : UnitMod Spec.P256.p (2^(64*c.K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve)
    (hn : (doubleSlots c.K.S c.K.R).Nodup)
    (hOne : c.K.one<Spec.P256.p) (hOneVal : toM Spec.P256.p (2^256) c.K.one=1)
    (hG : onCurve Spec.P256.curve G=true) (hQ : onCurve Spec.P256.curve Q=true)
    (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (hd : ScratchCT (doubleHalfPublic c.K.M c.K.S c.K.R)) (hu : u<2^256) (hv : v<2^256) :
    RelCT isa (JointPair c Spec.P256.curve base size
      (JointCore c Spec.P256.curve base size Q u v (JointGenerator c Spec.P256.curve base T size row)) .infinity 256)
      (Joint.run c (doubleHalfPublic c.K.M c.K.S c.K.R))
      (JointPair c Spec.P256.curve base size
        (JointCore c Spec.P256.curve base size Q u v (JointGenerator c Spec.P256.curve base T size row))
        (add (mul u G) (mul v Q)) 0) :=
  jointPair_run hL hm hC ha hOne hOneVal hG hQ (p256_jointOpsTiming hL hm hOne hc hf hd)
    (fun _ _ hp hi => jointDouble_core_ok hL.lookup.layout hm hC ha hn hp hi) hu hv

end VG.Proof.P256.X86_64
