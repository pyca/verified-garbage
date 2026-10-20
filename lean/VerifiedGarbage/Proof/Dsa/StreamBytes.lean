module

import VerifiedGarbage.Proof.Dsa.Digest
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Dsa

/-! # Streaming big-endian prefixes for DSA reduction -/

@[expose] public section
namespace VG.Proof.Dsa
open VG

theorem decode_prefix_succ (mem : Mem) (p : Addr) (i : Nat) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem p (i + 1)) =
      256 * Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem p i) + (mem (p + BitVec.ofNat 64 i)).toNat := by
  have bytes : Spec.Rsa.bytesAt mem p (i + 1) = Spec.Rsa.bytesAt mem p i ++ [mem (p + BitVec.ofNat 64 i)] := by
    simp only [Spec.Rsa.bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [bytes, decodeBE_append]
  simp only [List.length_cons, List.length_nil, Nat.pow_one, Spec.Dsa.decodeBE, List.foldl_cons, List.foldl_nil,
    Nat.mul_zero, Nat.zero_add]
  rw [Nat.mul_comm]

theorem reduce_prefix_succ (mem : Mem) (p : Addr) (i m : Nat) :
    (256 * (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem p i) % m) + (mem (p + BitVec.ofNat 64 i)).toNat) % m =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem p (i + 1)) % m := by
  rw [decode_prefix_succ]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

end VG.Proof.Dsa
