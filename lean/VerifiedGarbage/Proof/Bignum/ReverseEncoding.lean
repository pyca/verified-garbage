module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Rsa.Octets

/-! # Byte reversal implements RSA's OS2IP -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem reversed_read (m m' : Mem) (p q : Addr) (n : Nat)
    (bytes : ∀ j < n, m' (q + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 (n - 1 - j))) :
    (m'.read q n).toNat = Spec.Rsa.os2ip (Spec.Rsa.bytesAt m p n) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have last : m' q = m (p + BitVec.ofNat 64 n) := by
      simpa only [Nat.add_sub_cancel, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        using bytes 0 (by omega)
    have tail : ∀ j < n, m' (q + 1 + BitVec.ofNat 64 j) =
        m (p + BitVec.ofNat 64 (n - 1 - j)) := by
      intro j hj
      have h := bytes (j + 1) (by omega)
      rw [show q + 1 + BitVec.ofNat 64 j = q + BitVec.ofNat 64 (j + 1) by
        change q + BitVec.ofNat 64 1 + BitVec.ofNat 64 j = _
        rw [Offset.add_add, Nat.add_comm 1]]
      simpa only [show n + 1 - 1 - (j + 1) = n - 1 - j by omega] using h
    have snoc : Spec.Rsa.bytesAt m p (n + 1) =
        Spec.Rsa.bytesAt m p n ++ [m (p + BitVec.ofNat 64 n)] := by
      simp only [Spec.Rsa.bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [read_toNat_succ, last, ih (q + 1) tail, snoc, VG.Proof.Rsa.os2ip_snoc]
    omega

/-- Reversing a little-endian memory read produces its I2OSP encoding. -/
theorem reversed_i2osp (m m' : Mem) (p q : Addr) (n : Nat)
    (bytes : ∀ j < n, m' (q + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 (n - 1 - j))) :
    Spec.Rsa.bytesAt m' q n = Spec.Rsa.i2osp (m.read p n).toNat n := by
  have value : (m.read p n).toNat = Spec.Rsa.os2ip (Spec.Rsa.bytesAt m' q n) := by
    apply reversed_read
    intro j hj
    have h := bytes (n - 1 - j) (by omega)
    rw [show n - 1 - (n - 1 - j) = j by omega] at h
    exact h.symm
  rw [value]
  have len : (Spec.Rsa.bytesAt m' q n).length = n := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  simpa only [len] using (VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt m' q n)).symm

end VG.Proof.Bignum
