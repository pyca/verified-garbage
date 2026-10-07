import VerifiedGarbage.Impl.P384.X86_64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointFrame

/-! The joint multiplication's writes are apart from the final check's fixed inputs. -/
namespace VG.Proof.P384.X86_64
open VG VG.Impl.P384.X86_64 VG.Proof.Ecdsa.Verify.X86_64

theorem joint_frame_layout : JointFrameLayout p384v publicJoint := by
  constructor
  · unfold VG.Proof.Ecdsa.X86_64.FixedOk
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem joint_adx_frame_layout : JointFrameLayout p384vx publicJointAdx := by
  constructor
  · unfold VG.Proof.Ecdsa.X86_64.FixedOk
    decide +kernel
  · decide +kernel
  · decide +kernel

end VG.Proof.P384.X86_64
