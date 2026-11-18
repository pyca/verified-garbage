module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Points
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Lit
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Lit
meta import VerifiedGarbage.Proof.Framework.Taint

/-! The curve's rounds run in constant time (`taint_decide` on its code), and so does its loop, whatever
the peer: `JointKit.loop_ct` (`Proof/Ecdsa/Verify/AArch64/JointAll.lean`). -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

private theorem front_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19])) stepFront :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

private theorem tail_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x2])) digitTail :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem setup_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) setup :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- The two pieces of a round run in constant time. -/
theorem stepCt : JointKit.StepCt cfg := ⟨front_ct, tail_ct⟩

/-- The peers may differ: only the public digit pairs control the loop's trace. -/
theorem loop_ct {base : Addr} {P Q₁ Q₂ : Point C} {u v : Nat}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true)
    (hQ₁ : onCurve C Q₁=true) (hQ₂ : onCurve C Q₂=true) :
    RelCT isa (fun s t => Running base P Q₁ u v 128 s ∧ Running base P Q₂ u v 128 t ∧ s.sp=t.sp)
      (.loop step (.nonzero .x .x19))
      (fun s t => Running base P Q₁ u v 0 s ∧ Running base P Q₂ u v 0 t ∧ s.sp=t.sp) :=
  JointKit.loop_ct stepCt rounds hc hC hP hQ₁ hQ₂

end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
