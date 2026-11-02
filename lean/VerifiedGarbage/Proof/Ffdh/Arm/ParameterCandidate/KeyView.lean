module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

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
    96 + VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j = Proof.Rsa.Mont.arrAt w j := by
  change 96 + (160 + j * VG.Proof.Rsa.Arm.Keys.S (2 * w + 2)) = 256 + j * (8 * (w + 2))
  rw [keyView_stride]
  omega

theorem keyView_number (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32) :
    VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j =
      Proof.Rsa.Mont.numAt m (State.addr base) w j +
        2 ^ (64 * w) * val32 m (State.addr base) (Proof.Rsa.Mont.arrAt w j + 8 * w) 2 := by
  unfold VG.Proof.Rsa.Arm.Keys.num
  rw [VG.Arm.addr_add fits, VG.Proof.Rsa.Arm.CrtValues.val32_off, keyView_array, val32_append,
    VG.Proof.Bignum.Arm.numAt_native,
    show 32 * (2 * w) = 64 * w by omega, show 4 * (2 * w) = 8 * w by omega]

theorem keyView_low (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32) :
    val32 m (State.addr (base + 96#32)) (VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j) (2 * w) =
      Proof.Rsa.Mont.numAt m (State.addr base) w j := by
  rw [VG.Arm.addr_add fits, VG.Proof.Rsa.Arm.CrtValues.val32_off, keyView_array,
    VG.Proof.Bignum.Arm.numAt_native]

theorem numAt_lt (m : Mem) (base : Addr) (w j : Nat) :
    Proof.Rsa.Mont.numAt m base w j < 2 ^ (64 * w) := by
  have bound := (m.read (base + BitVec.ofNat 64 (Proof.Rsa.Mont.arrAt w j)) (8 * w)).isLt
  change _ < 2 ^ (8 * (8 * w)) at bound
  simpa only [Proof.Rsa.Mont.numAt, show 8 * (8 * w) = 64 * w by omega] using bound

theorem keyView_number_mod (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32) :
    VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j % 2 ^ (64 * w) =
      Proof.Rsa.Mont.numAt m (State.addr base) w j := by
  rw [keyView_number m base w j fits, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (numAt_lt m (State.addr base) w j)]

theorem keyView_number_low (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32)
    (small : VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j < 2 ^ (64 * w)) :
    Proof.Rsa.Mont.numAt m (State.addr base) w j =
      VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j := by
  have split := keyView_number m base w j fits
  have top : val32 m (State.addr base) (Proof.Rsa.Mont.arrAt w j + 8 * w) 2 = 0 := by
    by_contra nonzero
    have scale := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 1 ≤
      val32 m (State.addr base) (Proof.Rsa.Mont.arrAt w j + 8 * w) 2 by omega)
    rw [Nat.mul_one] at scale
    omega
  rw [top, Nat.mul_zero, Nat.add_zero] at split
  exact split.symm

theorem keyView_number_zeroTop (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32)
    (top : val32 m (State.addr base) (Proof.Rsa.Mont.arrAt w j + 8 * w) 2 = 0) :
    VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j =
      Proof.Rsa.Mont.numAt m (State.addr base) w j := by
  rw [keyView_number m base w j fits, top, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Ffdh.Arm.ParameterCandidate
