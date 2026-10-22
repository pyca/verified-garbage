module

public import VerifiedGarbage.Spec.Ffdh.SievedCandidate
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ScreenedStream
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The FFDH candidate on i686: its checks against the specification

The congruences of each generator (`gen2_eq`, `gen5_eq`), RSA's sieve on an
odd number past its primes (`sieve_shape`), and `sievedParameterCandidate`
for too short a tape, a rejected candidate and one that goes on to its
tests (`sieved_short`, `sieved_reject`, `sieved_tests`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.Spec.Ffdh VG.Proof.Ffdh.ParameterCandidate

/-- The table's sieve on an odd number past its primes: `primeShape` and RSA's sieve. -/
theorem sieve_shape {c bits : Nat} (hc : 8161 < c) (ho : c % 2 = 1) :
    (!VG.Proof.RsaKeyGen.trialPrefix c (sieveCount bits)) =
      (primeShape c && !Spec.RsaKeyGen.obviouslyComposite bits c) := by
  rw [← trialPrefix_sieveCount (bits := bits) hc, primeShape_sieve hc ho]
  by_cases hit : VG.Proof.RsaKeyGen.trialPrefix c (sieveCount bits) = true
  · simp only [hit, Bool.not_true, Bool.and_false]
  · have small : ((List.range 53).any fun i => c % VG.Impl.RsaKeyGen.tabEntry i == 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      apply hit
      simp only [List.any_eq_true, List.mem_range, beq_iff_eq] at h
      obtain ⟨i, hi, hd⟩ := h
      simp only [VG.Proof.RsaKeyGen.trialPrefix, List.any_eq_true, List.mem_range,
        VG.Proof.RsaKeyGen.entryDivides, decide_eq_true_eq]
      exact ⟨i, by unfold sieveCount; split <;> omega, hd⟩
    simp only [Bool.eq_false_iff.mpr hit, small, Bool.not_false, Bool.and_self]

/-- The shape for the generator 2: `p mod 8 = 3` and `3 | p − 2`. -/
theorem gen2_eq {bits p : Nat} (hb : 512 ≤ bits ∧ bits ≤ 8192) (hl : Spec.RsaKeyGen.bitLength p = bits)
    (hp : 2 ≤ p) : generationShape bits 2 p = (decide (p % 8 = 3) && decide ((p - 2) % 3 = 0)) := by
  unfold generationShape
  simp only [hl, show (512 ≤ bits) = True from propext ⟨fun _ => trivial, fun _ => hb.1⟩,
    show (bits ≤ 8192) = True from propext ⟨fun _ => trivial, fun _ => hb.2⟩, decide_true, beq_self_eq_true,
    Bool.true_and, ↓reduceIte]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The shape for the generator 5, of an odd p: `5 | p − 2` or `5 | p − 3`. -/
theorem gen5_eq {bits p : Nat} (hb : 512 ≤ bits ∧ bits ≤ 8192) (hl : Spec.RsaKeyGen.bitLength p = bits)
    (hp : 3 ≤ p) (ho : p % 2 = 1) :
    generationShape bits 5 p = (decide ((p - 2) % 5 = 0) || decide ((p - 3) % 5 = 0)) := by
  unfold generationShape
  simp only [hl, show (512 ≤ bits) = True from propext ⟨fun _ => trivial, fun _ => hb.1⟩,
    show (bits ≤ 8192) = True from propext ⟨fun _ => trivial, fun _ => hb.2⟩, decide_true, beq_self_eq_true,
    Bool.true_and, show ((5 : Nat) == 2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- Too short a tape for the candidate. -/
theorem sieved_short {bits g : Nat} {r : Spec.RsaKeyGen.Rand} (h : r.length < (bits + 7) / 8) :
    sievedParameterCandidate bits g r = none := by
  unfold sievedParameterCandidate
  rw [draw_of_short h]
  rfl

/-- A candidate its shape or sieve rejects. -/
theorem sieved_reject {bits g : Nat} {r : Spec.RsaKeyGen.Rand} (h : (bits + 7) / 8 ≤ r.length)
    (hr : (generationShape bits g (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      primeShape (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      primeShape ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2) &&
      !Spec.RsaKeyGen.obviouslyComposite bits (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      !Spec.RsaKeyGen.obviouslyComposite bits
        ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2)) = false) :
    sievedParameterCandidate bits g r = some (none, r.drop ((bits + 7) / 8)) := by
  unfold sievedParameterCandidate
  rw [draw_of_le h]
  simp only [bind, Option.bind_some, hr, Bool.not_false, ↓reduceIte]
  rfl

/-- A candidate past its shape and sieve: the result of its tests. -/
theorem sieved_tests {bits g : Nat} {r : Spec.RsaKeyGen.Rand} (h : (bits + 7) / 8 ≤ r.length)
    (hr : (generationShape bits g (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      primeShape (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      primeShape ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2) &&
      !Spec.RsaKeyGen.obviouslyComposite bits (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      !Spec.RsaKeyGen.obviouslyComposite bits
        ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2)) = true) :
    sievedParameterCandidate bits g r =
      (screenedChecks (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))))
        ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2) (r.drop ((bits + 7) / 8))).map
        fun x => (if x.1 then some (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) else none, x.2) := by
  have hs : primeShape (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) = true ∧
      primeShape ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2) = true := by
    simp only [Bool.and_eq_true] at hr
    exact ⟨hr.1.1.1.2, hr.1.1.2⟩
  rw [screenedChecks_eq hs.1 hs.2]
  unfold sievedParameterCandidate
  rw [draw_of_le h]
  simp only [bind, Option.bind_some, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases screenedParameterWitnesses _ _ _ with
  | none => rfl
  | some x => rfl

end VG.Proof.Ffdh.X86.Cand
