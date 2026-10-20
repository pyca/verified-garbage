module
public import VerifiedGarbage.Proof.Bignum.Arm.PdChecked

import VerifiedGarbage.Proof.Bignum.PublicWritten
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Arm.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Arm.PublicWritten

/-! # The packed-key result implies the shared, modulus-quantified RSA postcondition -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem pdOutput_written {s t : State} {dst pp : BitVec 32} {k : Nat} {nb eb xb : List Byte}
    (hk : 64 ≤ k) (hl : nb.length = k)
    (pre : Spec.Rsa.publicPrecompute nb = some (Spec.Rsa.wordsAt s.mem (State.addr pp) (2 * Spec.Rsa.modulusWords k)))
    (result : if Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) then
      PdOutput dst k (s.mem.read (State.addr pp) (8 * Spec.Rsa.modulusWords k)).toNat
        (s.mem.read (off (State.addr pp) (8 * Spec.Rsa.modulusWords k)) (8 * Spec.Rsa.modulusWords k)).toNat eb xb t
      else t.gpr .r0 = 0 ∧ Spec.Rsa.bytesAt t.mem (State.addr dst) k = List.replicate k 0) :
    Spec.Rsa.written t.mem (State.addr dst) k (t.gpr .r0) (Spec.Rsa.publicOpChecked nb eb xb) := by
  obtain ⟨valid, modulus, r2⟩ := VG.Proof.Bignum.pre_of_some hl hk pre
  have first : (s.mem.read (State.addr pp) (8 * Spec.Rsa.modulusWords k)).toNat = Spec.Rsa.os2ip nb := by
    have read := read_eq_wv s.mem (State.addr pp) 0 (Spec.Rsa.modulusWords k)
    simp only [off, BitVec.add_zero] at read
    exact read.trans modulus
  have second : (s.mem.read (off (State.addr pp) (8 * Spec.Rsa.modulusWords k)) (8 * Spec.Rsa.modulusWords k)).toNat =
      2 ^ (128 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip nb :=
    (read_eq_wv _ _ _ _).trans r2
  by_cases exponent : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true
  · simp only [exponent, ite_true] at result
    rw [first, second] at result
    obtain ⟨odd, large, _⟩ := VG.Proof.Bignum.valid_facts valid hk
    have positive : 0 < Spec.Rsa.os2ip nb := by omega
    have accepted : pdAccepted (Spec.Rsa.os2ip nb) (2 ^ (128 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip nb) = true := by
      simp only [pdAccepted, decide_eq_true large, decide_eq_true (Nat.mod_lt _ positive), decide_eq_true odd, Bool.and_true]
    have bound : Spec.Rsa.os2ip nb < 2 ^ (8 * k) := by
      have h := VG.Proof.Bignum.os2ip_lt nb
      rw [hl, VG.Proof.Bignum.pow256_eq] at h
      exact h
    obtain ⟨bytes, status⟩ := result accepted rfl bound
    exact publicOutput_written hl valid exponent bytes status
  · have invalid : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = false := by simpa using exponent
    simp only [invalid, Bool.false_eq_true, ite_false] at result
    have failed : Spec.Rsa.publicOpChecked nb eb xb = none := by simp [Spec.Rsa.publicOpChecked, invalid]
    rw [failed]
    exact result
end VG.Proof.Bignum.Arm
