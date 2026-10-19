module

public import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
public import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Read

/-! # The memory frame of ARMv7 packed-limb zeroing -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
export VG.Proof.Bignum (read_eq_val32 byte_zero_of_val32 read_zero_bytes val32_zero_extension)
open VG VG.Arm VG.Proof.Mont

theorem ZeroInv.frame {s0 s : State} {base : BitVec 32} {n : Nat}
    (inv : ZeroInv s0 base 0 n n s) :
    Frame [⟨State.addr base, 4 * n⟩] s0.mem s.mem := by
  intro a ha
  have h := ha ⟨State.addr base, 4 * n⟩ (by simp)
  change ¬ ((a - State.addr base).toNat + 1 ≤ 4 * n) at h
  exact inv.outside a (by simp only [ofs]; omega)

end VG.Proof.Bignum.Arm
