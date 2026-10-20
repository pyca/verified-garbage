module

import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoad
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.Words

/-! # The sieve's word loop branches only at the public end pointer -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

theorem word_address (p : BitVec 32) {n i : Nat} (fit : p.toNat + 4 * n ≤ 2 ^ 32) (index : i < n) :
    addr (p + BitVec.ofNat 32 (4 * i)) 0 = off (byteAddr p) (4 * i) := by
  change byteAddr (p + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = _
  rw [BitVec.add_zero, byteAddr_add (by omega)]

theorem pointer_zf (p : BitVec 32) {n i : Nat} (lengthBound : 4 * n < 2 ^ 32) (index : i < n) :
    (p + BitVec.ofNat 32 (4 * (i + 1)) - (p + BitVec.ofNat 32 (4 * n)) == 0) = decide (i + 1 = n) := by
  by_cases done : i + 1 = n
  · rw [done, BitVec.sub_self, decide_eq_true rfl]
    rfl
  · have different : p + BitVec.ofNat 32 (4 * (i + 1)) ≠ p + BitVec.ofNat 32 (4 * n) := by
      intro equal
      have small := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp equal)
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 4 * (i + 1) < 2 ^ 32),
        Nat.mod_eq_of_lt lengthBound] at small
      omega
    have nonzero : p + BitVec.ofNat 32 (4 * (i + 1)) - (p + BitVec.ofNat 32 (4 * n)) ≠ 0 := by
      intro zero
      apply different
      calc p + BitVec.ofNat 32 (4 * (i + 1)) =
          (p + BitVec.ofNat 32 (4 * (i + 1)) - (p + BitVec.ofNat 32 (4 * n))) +
            (p + BitVec.ofNat 32 (4 * n)) := (BitVec.sub_add_cancel _ _).symm
        _ = p + BitVec.ofNat 32 (4 * n) := by rw [zero]; exact BitVec.zero_add _
    rw [beq_eq_false_iff_ne.mpr nonzero, decide_eq_false done]

end VG.Proof.RsaKeyGen.X86.Trial
