module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Spec.Rsa.Mont
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! View the same Montgomery arrays through RSA's native key-operation
helpers. The 96-byte base adjustment aligns their 160-byte header with
the Montgomery header's 256 bytes. Two extra native words stay explicit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont

theorem keyView_stride (w : Nat) : VG.Proof.Rsa.Arm.Keys.S (2 * w + 2) = 8 * (w + 2) := by
  simp only [VG.Proof.Rsa.Arm.Keys.S]
  omega

theorem keyView_array (w j : Nat) :
    96 + VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j = Spec.Rsa.Mont.arrAt w j := by
  change 96 + (160 + j * VG.Proof.Rsa.Arm.Keys.S (2 * w + 2)) = 256 + j * (8 * (w + 2))
  rw [keyView_stride]
  omega

theorem keyView_number (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32) :
    VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j =
      Spec.Rsa.Mont.numAt m (State.addr base) w j +
        2 ^ (64 * w) * val32 m (State.addr base) (Spec.Rsa.Mont.arrAt w j + 8 * w) 2 := by
  unfold VG.Proof.Rsa.Arm.Keys.num
  rw [VG.Arm.addr_add fits, VG.Proof.Rsa.Arm.CrtValues.val32_off, keyView_array, val32_append,
    VG.Proof.Bignum.Arm.numAt_native,
    show 32 * (2 * w) = 64 * w by omega, show 4 * (2 * w) = 8 * w by omega]

theorem keyView_number_zeroTop (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32)
    (top : val32 m (State.addr base) (Spec.Rsa.Mont.arrAt w j + 8 * w) 2 = 0) :
    VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j =
      Spec.Rsa.Mont.numAt m (State.addr base) w j := by
  rw [keyView_number m base w j fits, top, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Ffdh.Arm.ParameterCandidate
