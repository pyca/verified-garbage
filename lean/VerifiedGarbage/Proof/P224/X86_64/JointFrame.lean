module

public import VerifiedGarbage.Impl.P224.X86_64.Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointFrame
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-! The joint multiplication's writes are apart from the final check's fixed inputs. -/

@[expose] public section

namespace VG.Proof.P224.X86_64
open VG VG.Impl.P224.X86_64 VG.Proof.Ecdsa.Verify.X86_64

theorem joint_frame_layout : JointFrameLayout p224v publicJoint := by
  constructor
  · unfold VG.Proof.Ecdsa.X86_64.FixedOk
    decide +kernel
  · decide +kernel
  · decide +kernel

end VG.Proof.P224.X86_64
