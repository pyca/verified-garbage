module

import VerifiedGarbage.Proof.Framework.PowLit

import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Framework.Omega

/-! # A trial hit masks the remaining sieve count to zero -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG

def nextCount (q : Nat) (hit : Bool) : Nat := if hit then 0 else q - 1

theorem nextCount_word {q : Nat} (positive : 0 < q) (bound : q < 2 ^ 32) (hit : Bool) :
    (BitVec.ofNat 32 q - 1) &&& (BitVec.ofNat 32 hit.toNat - 1) = BitVec.ofNat 32 (nextCount q hit) := by
  cases hit with
  | false =>
    change (BitVec.ofNat 32 q - 1) &&& BitVec.allOnes 32 = BitVec.ofNat 32 (q - 1)
    rw [BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  | true =>
    change (BitVec.ofNat 32 q - 1) &&& 0#32 = 0#32
    exact BitVec.and_zero

theorem nextCount_lt {q : Nat} (positive : 0 < q) (hit : Bool) : nextCount q hit < q := by
  cases hit <;> simp [nextCount] <;> omega

theorem nextCount_zero {q : Nat} (positive : 0 < q) (hit : Bool) :
    nextCount q hit = 0 ↔ hit = true ∨ q = 1 := by
  cases hit <;> simp [nextCount] <;> omega

theorem countWord_zero {n : Nat} (bound : n < 2 ^ 32) :
    (BitVec.ofNat 32 n == 0#32) = decide (n = 0) := by
  rw [Bool.beq_eq_decide_eq]
  apply decide_eq_decide.mpr
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  rfl

end VG.Proof.RsaKeyGen.X86.Sieve
