module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! The low three bits of a nonempty big-endian candidate are the low
three bits of its final octet. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Mont

private theorem bytesAt_snoc (m : Mem) (base : Addr) {n : Nat} (positive : 0 < n) :
    Spec.Rsa.bytesAt m base n = Spec.Rsa.bytesAt m base (n - 1) ++ [m (off base (n - 1))] := by
  calc
    _ = Spec.Rsa.bytesAt m base ((n - 1) + 1) := congrArg _ (by omega : n = (n - 1) + 1)
    _ = _ := by
      simp only [Spec.Rsa.bytesAt, List.map_append, List.range_succ,
        List.map_nil, List.map_cons, off]

theorem candidate_mod8_last (m : Mem) (base : Addr) {n : Nat} (positive : 0 < n) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt m base n) % 8 = (m (off base (n - 1))).toNat % 8 := by
  rw [bytesAt_snoc m base positive, VG.Proof.Ffdh.KeyScalar.os2ip_append]
  have singleton (b : Byte) : Spec.Rsa.os2ip [b] = b.toNat := by simp [Spec.Rsa.os2ip]
  rw [singleton]
  simp only [List.length_singleton, Nat.pow_one]
  rw [Nat.add_mod, Nat.mul_mod, show 256 % 8 = 0 by decide, Nat.mul_zero, Nat.zero_mod,
    Nat.zero_add, Nat.mod_mod]

theorem residue24 {n : Nat} : n % 24 = 11 ↔ n % 8 = 3 ∧ n % 3 = 2 := by omega

theorem residue10 {n : Nat} (odd : n % 2 = 1) :
    (n % 10 = 3 ∨ n % 10 = 7) ↔ n % 5 = 2 ∨ n % 5 = 3 := by omega

end VG.Proof.Ffdh.Arm.ParameterCandidate
