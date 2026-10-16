module

public import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Rsa.Octets
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Byte reversal implements RSA's OS2IP -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

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

/-- The complete loop computes the integer of the original big-endian input. -/
theorem ReverseInv.os2ip {s0 s : State} {src dst : BitVec 32} {n : Nat}
    (inv : ReverseInv s0 (src + BitVec.ofNat 32 (n - 1)) dst n n s)
    (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32) :
    (s.mem.read (State.addr dst) n).toNat = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (State.addr src) n) := by
  apply reversed_read
  intro j hj
  have h := inv.copied j hj
  rw [addr_add (by omega), reverse_source_addr src srcFit hj] at h
  exact h

end VG.Proof.Bignum.Arm
