module

public import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-! # Bytewise wrapped addition for DSA's hashed seeds -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

/-- Adding a public offset to a seed propagates a carry from the last byte.
Fixed-width encoding discards the final carry, exactly as required by DSA. -/
theorem seedAdd_snoc (bs : List Byte) (b : Byte) (carry : Nat) :
    Spec.Dsa.encodeBE (bs.length + 1) (Spec.Dsa.decodeBE (bs ++ [b]) + carry) =
      Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + (b.toNat + carry) / 256) ++
        [BitVec.ofNat 8 (b.toNat + carry)] := by
  rw [encodeBE_i2osp, decodeBE_os2ip, VG.Proof.Rsa.os2ip_snoc,
    VG.Proof.Rsa.i2osp_succ, encodeBE_i2osp, decodeBE_os2ip]
  congr 2
  · rw [Nat.add_assoc, Nat.mul_add_div (by decide)]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.add_mod, Nat.mul_mod, Nat.mod_self,
      Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]

/-- Empty seeds discard the carry too. -/
theorem seedAdd_nil (carry : Nat) : Spec.Dsa.encodeBE 0 carry = [] := rfl

end VG.Proof.Dsa.Generation
