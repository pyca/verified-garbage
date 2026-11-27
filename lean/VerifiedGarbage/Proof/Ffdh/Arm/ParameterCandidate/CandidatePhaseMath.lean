module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Spec.Ffdh

/-! ### `Ffdh.Arm.ParameterCandidate.PhaseState`, which this module and modules that import it used -/

section

/-! The public parameter-generation phase's four saved policy words. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

def phaseBits (q : Bool) (bits : Nat) : Nat := if q then bits - 1 else bits

def phaseMemory (s : State) (q : Bool) (bits : Nat) : Mem :=
  (((s.mem.writeW (State.addr (s.sp + 44#32)) (BitVec.ofNat 32 (phaseBits q bits))).writeW
    (State.addr (s.sp + 48#32)) (BitVec.ofNat 32 ((phaseBits q bits + 7) / 8))).writeW
    (State.addr (s.sp + 52#32)) (BitVec.ofNat 32 (VG.Spec.Ffdh.primeChecks (phaseBits q bits)))).writeW
    (State.addr (s.sp + 56#32)) (0#32)



end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! q and p share the fixed p-width RSA workspace and the same entropy tape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

def candidatePhase (p : CandidateParams) (q : Bool) : WitnessParams where
  base := p.base
  tape := p.tape
  capacity := p.capacity
  words := p.words
  modulus := if q then (p.candidate - 1) / 2 else p.candidate
  bits := phaseBits q p.bits
  checks := Spec.Ffdh.primeChecks (phaseBits q p.bits)
  bytes := p.bytes

theorem CandidateParams.phase_large (p : CandidateParams) (q : Bool) : 1 < (candidatePhase p q).modulus := by
  obtain ⟨odd, lower, upper⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape
    (by have := p.minBits; omega_using [this] : 2 ≤ p.bits) (Spec.Rsa.os2ip (p.bytes.take p.length))
  obtain ⟨halfLower, _⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by have := p.minBits; omega_using [this]) odd lower upper
  have lowP : 2 ^ 2 ≤ 2 ^ (p.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := p.minBits; omega_using [this])
  have lowQ : 2 ^ 2 ≤ 2 ^ (p.bits - 2) := Nat.pow_le_pow_right (by decide) (by have := p.minBits; omega_using [this])
  change 1 < if q then (p.candidate - 1) / 2 else p.candidate
  change 2 ^ (p.bits - 1) ≤ p.candidate at lower
  change 2 ^ (p.bits - 2) ≤ (p.candidate - 1) / 2 at halfLower
  change 4 ≤ 2 ^ (p.bits - 1) at lowP
  change 4 ≤ 2 ^ (p.bits - 2) at lowQ
  cases q <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega_arith

theorem CandidateParams.phase_normalized (p : CandidateParams) (q : Bool) :
    p.length % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords p.length - 1)) ≤
      (candidatePhase p q).modulus := by
  by_cases boundary : p.length % 8 = 1
  · exact Or.inl boundary
  right
  obtain ⟨odd,lower,upper⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape
    (by have := p.minBits; omega_using [this] : 2 ≤ p.bits) (Spec.Rsa.os2ip (p.bytes.take p.length))
  obtain ⟨halfLower,_⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape
    (by have := p.minBits; omega_using [this]) odd lower upper
  have exponent : 64 * (Spec.Rsa.modulusWords p.length - 1) ≤ p.bits - 2 := by
    have := p.minBits
    dsimp only [CandidateParams.length,Spec.Rsa.modulusWords] at *
    omega_using [boundary]
  have power := Nat.pow_le_pow_right (n := 2) (by decide) exponent
  have powerP := Nat.pow_le_pow_right (n := 2) (by decide) (show p.bits - 2 ≤ p.bits - 1 by omega_using [])
  change 2 ^ (p.bits - 1) ≤ p.candidate at lower
  change 2 ^ (p.bits - 2) ≤ (p.candidate - 1) / 2 at halfLower
  cases q
  · exact Nat.le_trans power (Nat.le_trans powerP lower)
  · exact Nat.le_trans power halfLower

theorem CandidateParams.phase_bits_exact (p : CandidateParams) (q : Bool)
    (odd : (candidatePhase p q).modulus % 2 = 1) :
    (candidatePhase p q).bits = Spec.RsaKeyGen.bitLength ((candidatePhase p q).modulus - 1) := by
  cases q
  · exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := p.bits)
      (by have := p.minBits; omega_using [this]) (Spec.Rsa.os2ip (p.bytes.take p.length))).2.symm
  · exact (VG.Proof.Ffdh.ParameterCandidate.half_pred_bitLength (bits := p.bits)
      (by have := p.minBits; omega_using [this]) (Spec.Rsa.os2ip (p.bytes.take p.length)) odd).symm

theorem CandidateParams.phase_bounds (p : CandidateParams) (q : Bool) :
    0 < (candidatePhase p q).bits ∧ (candidatePhase p q).bits ≤ 8192 ∧
    (candidatePhase p q).bits ≤ 64 * p.words ∧
    0 < (candidatePhase p q).checks ∧ (candidatePhase p q).checks ≤ 128 := by
  have low := p.minBits
  have high := p.maxBits
  have bitsFit : p.bits ≤ 64 * p.words := by
    dsimp only [CandidateParams.words, CandidateParams.length, Spec.Rsa.modulusWords]
    omega_using []
  have phaseFit : phaseBits q p.bits ≤ p.bits := by cases q <;> simp [phaseBits]
  have phasePositive : 0 < phaseBits q p.bits := by cases q <;> simp [phaseBits] <;> omega_using [low]
  have count : 0 < Spec.Ffdh.primeChecks (phaseBits q p.bits) ∧
      Spec.Ffdh.primeChecks (phaseBits q p.bits) ≤ 128 := by
    unfold Spec.Ffdh.primeChecks
    split <;> decide
  exact ⟨phasePositive, by change phaseBits q p.bits ≤ 8192; omega_using [high, phaseFit],
    by change phaseBits q p.bits ≤ 64 * p.words; omega_using [bitsFit, phaseFit], count⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
