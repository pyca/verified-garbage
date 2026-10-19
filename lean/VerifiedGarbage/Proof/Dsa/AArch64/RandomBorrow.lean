module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Byte-subtraction lemma used by the scalar range check. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64

/-- For byte-sized operands (including an incoming borrow), the high bit of
64-bit subtraction is precisely the unsigned borrow. -/
theorem random_byte_borrow (a b : BitVec 64) (ha : a.toNat ≤ 255) (hb : b.toNat ≤ 256) :
    ((a - b) >>> 63).toNat = if a.toNat < b.toNat then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  split <;> omega

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Bignum.AArch64

/-- The actual instruction block computes the outgoing byte borrow. -/
theorem random_borrow_ok (s : State)
    (ha : (s.gpr .x0).toNat ≤ 255) (hb : (s.gpr .x4).toNat ≤ 255)
    (hc : (s.gpr .x8).toNat ≤ 1) :
    WP isa (.block Impl.Dsa.AArch64.Random.borrow) s fun t =>
      (t.gpr .x8).toNat =
        (if (s.gpr .x0).toNat < (s.gpr .x4).toNat + (s.gpr .x8).toNat then 1 else 0) ∧
      t.mem = s.mem := by
  have hadd : (s.gpr .x4 + s.gpr .x8).toNat = (s.gpr .x4).toNat + (s.gpr .x8).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hbound : (s.gpr .x4 + s.gpr .x8).toNat ≤ 256 := by rw [hadd]; omega
  have hborrow := random_byte_borrow (s.gpr .x0) (s.gpr .x4 + s.gpr .x8) ha hbound
  rw [hadd] at hborrow
  unfold Impl.Dsa.AArch64.Random.borrow
  brun [hborrow]

end VG.Proof.Dsa.AArch64
