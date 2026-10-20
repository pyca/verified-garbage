module

public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! Byte-subtraction lemma used by the scalar range check. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64

/-- For byte-sized operands (including an incoming borrow), the high bit of
64-bit subtraction is precisely the unsigned borrow. -/
theorem random_byte_borrow (a b : BitVec 64) (ha : a.toNat ≤ 255) (hb : b.toNat ≤ 256) :
    ((a - b) >>> 63).toNat = if a.toNat < b.toNat then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  split <;> omega

open VG VG.X86_64 VG.Proof.MlKem.X86_64

end VG.Proof.Dsa.X86_64
