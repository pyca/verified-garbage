import VerifiedGarbage.Impl.P521.X86_64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointFrame

/-! The joint multiplication's writes are apart from the final check's fixed inputs. -/
namespace VG.Proof.P521.X86_64
open VG VG.Impl.P521.X86_64 VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.Verify.X86_64

theorem joint_frame_layout : JointFrameLayout p521 publicJoint := by
  constructor
  · unfold VG.Proof.Ecdsa.X86_64.FixedOk
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem joint_adx_frame_layout : JointFrameLayout p521x publicJointAdx := by
  constructor
  · unfold VG.Proof.Ecdsa.X86_64.FixedOk
    decide +kernel
  · decide +kernel
  · decide +kernel

end VG.Proof.P521.X86_64
