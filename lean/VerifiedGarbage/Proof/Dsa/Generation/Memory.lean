module

public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-! # Byte buffers used by DSA's parameter search on both architectures -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Proof.Bignum

theorem bytesAt_append (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (off p a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_def, off, BitVec.ofNat_add, BitVec.add_assoc]

theorem frame_bytesAt {m m' : Mem} {rs : List Region} {p : Addr} {len : Nat}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes hd hl (List.mem_range.mp hi)

/-- Reading the final b bytes performs reduction modulo their byte width. -/
theorem bytesAt_suffix_value (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m p (a + b)) % 256 ^ b =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off p a) b) := by
  rw [bytesAt_append, decodeBE_append, bytesAt_length, Nat.mul_comm _ (256 ^ b), Nat.mul_add_mod,
    Nat.mod_eq_of_lt (by simpa only [bytesAt_length] using decodeBE_lt (Spec.Rsa.bytesAt m (off p a) b))]

end VG.Proof.Dsa.Generation
