module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialSmall
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! The shared RSA radix-2^16 remainder is an ordinary remainder modulo
3 and 5, because its radix is 1 modulo either divisor. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem trialPrime3 : VG.Impl.RsaKeyGen.tabEntry 0 = 3 := by
  unfold VG.Impl.RsaKeyGen.tabEntry VG.Impl.RsaKeyGen.slots
  rw [VG.Impl.RsaKeyGen.primes.lit_eq]
  rfl

theorem trialPrime5 : VG.Impl.RsaKeyGen.tabEntry 1 = 5 := by
  unfold VG.Impl.RsaKeyGen.tabEntry VG.Impl.RsaKeyGen.slots
  rw [VG.Impl.RsaKeyGen.primes.lit_eq]
  rfl

private theorem radix_fixed {prime : Nat} (bound : prime < 2) (steps : Nat) :
    2 ^ (16 * steps) % VG.Impl.RsaKeyGen.tabEntry prime = 1 := by
  have fixed : 2 ^ 16 % VG.Impl.RsaKeyGen.tabEntry prime = 1 := by
    rcases (by omega : prime = 0 ∨ prime = 1) with rfl | rfl
    · rw [trialPrime3]
    · rw [trialPrime5]
  rw [Nat.pow_mul, Nat.pow_mod, fixed, Nat.one_pow]
  have positive : 1 < VG.Impl.RsaKeyGen.tabEntry prime := by
    rcases (by omega : prime = 0 ∨ prime = 1) with rfl | rfl
    · rw [trialPrime3]; decide
    · rw [trialPrime5]; decide
  exact Nat.mod_eq_of_lt positive

theorem trialSmall_residue_ok (s : State) (dst : BitVec 32) {n prime : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32) (bufferFits : dst.toNat + n ≤ 2 ^ 32)
    (primeBound : prime < 2)
    (divisor : s.gpr .r7 = BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))
    (readOut : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4)) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12)) 4)
    (out : s.mem.readW (State.addr (s.sp + 4)) 32 = dst)
    (width : s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n)
    (read : TrialReadable s (dst + BitVec.ofNat 32 n) n) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall s fun t =>
      ∃ next, next < 2 * VG.Impl.RsaKeyGen.tabEntry prime ∧ t.gpr .r2 = BitVec.ofNat 32 next ∧
        next % VG.Impl.RsaKeyGen.tabEntry prime =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % VG.Impl.RsaKeyGen.tabEntry prime ∧
        t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  refine WP.mono (trialSmall_value_ok s dst positive fits bufferFits (by omega) divisor
    readOut readWidth out width read) ?_
  rintro t ⟨next, steps, bound, value, congruence, _, memory, rest⟩
  have residue : next % VG.Impl.RsaKeyGen.tabEntry prime =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % VG.Impl.RsaKeyGen.tabEntry prime := by
    rw [Nat.mul_mod, radix_fixed primeBound steps, Nat.mul_one, Nat.mod_mod] at congruence
    exact congruence
  exact ⟨next, bound, value, residue, memory, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
