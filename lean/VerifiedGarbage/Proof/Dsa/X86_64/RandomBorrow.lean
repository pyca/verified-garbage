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

/-- The actual instruction block computes the outgoing byte borrow. -/
theorem random_borrow_ok (s : State)
    (ha : (s.gpr .rax).toNat ≤ 255) (hb : (s.gpr .rcx).toNat ≤ 255)
    (hc : (s.gpr .r8).toNat ≤ 1) :
    WP isa (.block Impl.Dsa.X86_64.Random.borrow) s fun t =>
      (t.gpr .r8).toNat =
        (if (s.gpr .rax).toNat < (s.gpr .rcx).toNat + (s.gpr .r8).toNat then 1 else 0) ∧
      t.mem = s.mem := by
  have hadd : (s.gpr .rcx + s.gpr .r8).toNat = (s.gpr .rcx).toNat + (s.gpr .r8).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hbound : (s.gpr .rcx + s.gpr .r8).toNat ≤ 256 := by rw [hadd]; omega
  have hborrow := random_byte_borrow (s.gpr .rax) (s.gpr .rcx + s.gpr .r8) ha hbound
  rw [hadd] at hborrow
  unfold Impl.Dsa.X86_64.Random.borrow
  xrun [hborrow]

end VG.Proof.Dsa.X86_64
