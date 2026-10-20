module
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.StreamBytes

/-! # Two-byte Horner reduction of a big-endian candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG

theorem trial_prefix_pair (m : Mem) (base : Addr) (i p : Nat) :
    ((Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m base i) % p) * 65536 +
      (m (base + BitVec.ofNat 64 i)).toNat * 256 + (m (base + BitVec.ofNat 64 (i + 1))).toNat) % p =
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m base (i + 2)) % p := by
  rw [show i + 2 = (i + 1) + 1 from rfl, VG.Proof.Dsa.decode_prefix_succ, VG.Proof.Dsa.decode_prefix_succ]
  simp only [Nat.mul_add, ← Nat.mul_assoc, Nat.reduceMul]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mul_comm]
end VG.Proof.Dsa.X86.Generation
