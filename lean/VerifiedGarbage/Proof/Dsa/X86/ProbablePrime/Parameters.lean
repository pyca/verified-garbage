module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Environment
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Width
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Enter
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Load
import VerifiedGarbage.Proof.RsaKeyGen.KeyCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! # The blinded loop's parameters for a DSA candidate

The loop of `Spec.Dsa.probablePrime` is RSA's with DSA's round count, its
witnesses read from the start of the tape and cut to the candidate's width.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86
open VG.Impl.Dsa.X86.ProbablePrime

def Environment.parameters (E : Environment) (c : Nat) (entropy : List Byte) : MillerRabinLoop.Parameters :=
  ⟨E.geometry, E.capacity, E.p - 28#32, E.rand, E.randLength, c, entropy,
    Spec.Dsa.primeChecks E.bits, 0, 8 * ((E.bits + 63) / 64), E.words, E.bits - 1⟩

/-- An odd number of `bits` bits lies above `2 ^ (bits - 1)`, and so does
its predecessor. -/
theorem candidate_shape {c bits : Nat} (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = bits)
    (two : 2 ≤ bits) : Spec.RsaKeyGen.bitLength (c - 1) = bits ∧ 2 ^ (bits - 1) < c ∧ c < 2 ^ bits := by
  have length' : Spec.RsaKeyGen.bitLength c = (bits - 1) + 1 := by
    rw [show bits - 1 + 1 = bits by omega]; exact length
  have low := VG.Proof.RsaKeyGen.le_of_bitLength length'
  have high := VG.Proof.RsaKeyGen.bitLength_lt (n := c) (b := bits) length
  have even : 2 ^ (bits - 1) % 2 = 0 := by
    rw [show bits - 1 = (bits - 2) + 1 by omega, Nat.pow_succ]
    omega
  have strict : 2 ^ (bits - 1) < c := by
    rcases Nat.lt_or_eq_of_le low with lt | eq
    · exact lt
    · rw [← eq] at odd; omega
  refine ⟨?_, strict, high⟩
  have := VG.Proof.RsaKeyGen.bitLength_of (n := c - 1) (b := bits - 1) (by omega)
    (by rw [show bits - 1 + 1 = bits by omega]; omega)
  rw [this]
  omega

theorem trialPrimes_eq {bits : Nat} (b : Bits bits) :
    Spec.RsaKeyGen.trialPrimes (64 * width bits) = Spec.RsaKeyGen.trialPrimes bits := by
  have := b.whole
  have := b.low
  unfold Spec.RsaKeyGen.trialPrimes width
  split <;> split <;> omega

theorem obviouslyComposite_eq {bits : Nat} (b : Bits bits) (c : Nat) :
    Spec.RsaKeyGen.obviouslyComposite (64 * width bits) c = Spec.RsaKeyGen.obviouslyComposite bits c := by
  unfold Spec.RsaKeyGen.obviouslyComposite
  rw [trialPrimes_eq b]

theorem lengthRegion_far {p : BitVec 32} (low : 136 ≤ p.toNat) (fit : p.toNat + 40 ≤ 2 ^ 32) :
    (lengthRegion (p - 28#32)).Disjoint (below (p - 28#32) 108) := by
  have privateNat : (p - 28#32).toNat = p.toNat - 28 := sub_toNat (by omega)
  have lengthNat : (lengthRegion (p - 28#32)).base.toNat = p.toNat - 4 := by
    change (((p - 28#32) + 24#32).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, privateNat]
    change ((p.toNat - 28 + 24) % 2 ^ 32) % 2 ^ 64 = p.toNat - 4
    have := p.isLt
    omega
  have belowNat : (below (p - 28#32) 108).base.toNat = p.toNat - 136 := by
    change (((p - 28#32) - 108#32).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, sub_toNat (by omega), privateNat]
    have := p.isLt
    omega
  apply Region.Disjoint.symm
  apply Offset.disjoint_of_le
  · change (below (p - 28#32) 108).base.toNat + 108 ≤ (lengthRegion (p - 28#32)).base.toNat
    rw [belowNat, lengthNat]; omega
  · change (lengthRegion (p - 28#32)).base.toNat + 4 ≤ 2 ^ 64
    rw [lengthNat]; have := p.isLt; omega

theorem Environment.Valid.parameters_valid {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte}
    (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits) (entropyLength : entropy.length = E.randLength) :
    (E.parameters c entropy).Valid := by
  have b := v.bits
  have low := v.low
  have shape := candidate_shape odd length (by have := b.low; omega)
  have inner : (below (E.p - 28#32) 108).Sub (below E.p 136) := below_inner (by decide) v.low
  have big : 2 ^ 63 ≤ 2 ^ (E.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := b.low; omega)
  refine ⟨v.geometry, rfl, v.randFit, v.randLengthFit, entropyLength, v.randWorkspace,
    (v.stackFar _ (List.mem_cons_of_mem _ List.mem_cons_self)).sub_right inner,
    by change 108 ≤ (E.p - 28#32).toNat; rw [sub_toNat (by omega)]; omega,
    (v.stackFar _ List.mem_cons_self).sub_right inner, lengthRegion_far v.low (by have := v.argsFit; omega),
    odd, by change 3 < c; omega, ?_, b.words_two, b.draw_ge, b.draw_le, by change 8 * _ % 4 = 0; omega,
    by change 1 ≤ E.bits - 1; have := b.low; omega, ?_, ?_, ?_⟩
  · change Spec.RsaKeyGen.bitLength (c - 1) = 32 * (E.bits / 32)
    rw [shape.1]; have := b.whole; omega
  · change E.bits - 1 < 64 * VG.Impl.Dsa.X86.ProbablePrime.width E.bits
    unfold VG.Impl.Dsa.X86.ProbablePrime.width; have := b.low; omega
  · change Spec.RsaKeyGen.witnessBytes c = 8 * ((E.bits + 63) / 64)
    unfold Spec.RsaKeyGen.witnessBytes
    rw [shape.1]
  · change Spec.Dsa.primeChecks E.bits < 2 ^ 32
    unfold Spec.Dsa.primeChecks
    split <;> decide

/-- Past trial division, `Spec.Dsa.probablePrime` is the blinded loop. -/
theorem probablePrime_eq {E : Environment} (v : E.Valid) {c : Nat} (entropy : List Byte)
    (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits)
    (composite : Spec.RsaKeyGen.obviouslyComposite E.bits c = false) :
    Spec.Dsa.probablePrime c entropy = (E.parameters c entropy).test := by
  have shape := candidate_shape odd length (by have := v.bits.low; omega)
  have big : 2 ^ 63 ≤ 2 ^ (E.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := v.bits.low; omega)
  have three : (c == 3) = false := by
    rw [beq_eq_false_iff_ne]; omega
  unfold Spec.Dsa.probablePrime
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by rw [three]; decide), length, composite]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rfl

end VG.Proof.Dsa.X86.ProbablePrime
