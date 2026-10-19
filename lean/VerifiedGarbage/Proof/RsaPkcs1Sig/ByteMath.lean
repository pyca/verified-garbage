module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.WriteBytes

/-! # Byte-list identities for signature encoders -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig
open VG VG.WriteBytes

theorem bytesAt_take_succ (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).take (i + 1) =
      (Spec.Rsa.bytesAt m p n).take i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp only [Spec.Rsa.bytesAt]
  rw [← List.map_take, ← List.map_take, List.take_range, List.take_range, Nat.min_eq_left (by omega),
    Nat.min_eq_left (by omega), List.range_succ, List.map_append]
  rfl

theorem writeBytes_out (m : Mem) (q a : Addr) (xs : List Byte) (k : Nat)
    (apart : ∀ i < k, a ≠ q + BitVec.ofNat 64 i) (bound : xs.length ≤ k) :
    writeBytes m q xs a = m a := by
  unfold writeBytes
  split
  · rename_i inside
    apply False.elim
    exact apart (a - q).toNat (by omega) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm q, BitVec.sub_add_cancel])
  · rfl

end VG.Proof.RsaPkcs1Sig
