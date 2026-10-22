module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessChecks

/-! # The public candidate environment supplies the complete blinded-loop geometry -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def Environment.parameters (E : Environment) (entropy : List Byte) : MillerRabinLoop.Parameters :=
  ⟨E.geometry, E.capacity, E.p - 28#32, E.rand, E.randLength, candidateValue E entropy, entropy,
    VG.Impl.RsaKeyGen.X86.WitnessChecks.checks E.width, 8 * E.width, 8 * E.width, 2 * E.width, 64 * E.width - 1⟩

theorem Environment.Valid.parameters_valid {E : Environment} (v : E.Valid) (entropy : List Byte)
    (entropyLength : entropy.length = E.randLength) : (E.parameters entropy).Valid := by
  have low := v.low
  have privateNat : (E.p - 28#32).toNat = E.p.toNat - 28 := sub_toNat (by omega)
  have privateFit : 68 ≤ (E.p - 28#32).toNat := by rw [privateNat]; omega
  have inner : (below (E.p - 28#32) 68).Sub (below E.p 96) := below_inner (by decide) v.low
  have bits := candidate_bits v entropy
  refine ⟨v.geometry, rfl, v.randFit, v.randLengthFit, entropyLength,
    v.readWorkspace (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), ?_, privateFit, ?_, ?_,
    candidate_odd v entropy, by change 3 < candidateValue E entropy; have := candidate_large v entropy; omega,
    by change Spec.RsaKeyGen.bitLength (candidateValue E entropy - 1) = 32 * (2 * E.width); rw [bits.2.1]; omega,
    by have := v.width_bounds; change 2 ≤ 2 * E.width; omega, by change 4 * (2 * E.width) ≤ 8 * E.width; omega,
    Nat.le_refl _, by change 8 * E.width % 4 = 0; omega, by have := v.width_bounds; change 1 ≤ 64 * E.width - 1; omega,
    by have := v.width_bounds; change 64 * E.width - 1 < 64 * E.width; omega, ?_, ?_⟩
  · exact (v.stackFar E.randRegion (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right inner
  · exact (v.stackFar E.workspaceRegion (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right inner
  · change (lengthRegion (E.p - 28#32)).Disjoint (below (E.p - 28#32) 68)
    have lengthNat : (lengthRegion (E.p - 28#32)).base.toNat = E.p.toNat - 4 := by
      change (((E.p - 28#32) + 24#32).setWidth 64).toNat = _
      rw [BitVec.toNat_setWidth, BitVec.toNat_add, privateNat]
      change ((E.p.toNat - 28 + 24) % 2 ^ 32) % 2 ^ 64 = E.p.toNat - 4
      have := E.p.isLt
      omega
    have belowNat : (below (E.p - 28#32) 68).base.toNat = E.p.toNat - 96 := by
      change (((E.p - 28#32) - 68#32).setWidth 64).toNat = _
      rw [BitVec.toNat_setWidth, sub_toNat privateFit, privateNat]
      have := E.p.isLt
      omega
    apply Region.Disjoint.symm
    apply Offset.disjoint_of_le
    · change (below (E.p - 28#32) 68).base.toNat + 68 ≤ (lengthRegion (E.p - 28#32)).base.toNat
      rw [belowNat, lengthNat]; omega
    · change (lengthRegion (E.p - 28#32)).base.toNat + 4 ≤ 2 ^ 64
      rw [lengthNat]; have := E.p.isLt; omega
  · change Spec.RsaKeyGen.witnessBytes (candidateValue E entropy) = 8 * E.width
    rw [bits.2.2, v.length_eq]
  · exact VG.Proof.RsaKeyGen.X86.WitnessChecks.checks_bound E.width

/-- The loop's result is RSA's primality test of the candidate. -/
theorem Environment.Valid.test_eq {E : Environment} (v : E.Valid) (entropy : List Byte) :
    (E.parameters entropy).test =
      Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop (8 * E.width)) := by
  have bits := candidate_bits v entropy
  have checks : Spec.RsaKeyGen.checksForSize (Spec.RsaKeyGen.bitLength (candidateValue E entropy)) =
      VG.Impl.RsaKeyGen.X86.WitnessChecks.checks E.width := by
    rw [bits.1]
    exact VG.Proof.RsaKeyGen.checksW_eq E.width (by have := v.width_bounds.2; omega) v.width_bounds.1
  have odd := candidate_odd v entropy
  have large := candidate_large v entropy
  unfold Spec.RsaKeyGen.primalityTest
  rw [ite_eq_right (by omega), ite_eq_right (by rw [odd]; decide), ite_eq_right (by omega), checks]
  rfl

theorem MemoryFacts.entropyLength {E : Environment} {eBytes pBytes entropy : List Byte} {s : State}
    (M : MemoryFacts E eBytes pBytes entropy s) : entropy.length = E.randLength := by
  rw [← M.entropy]
  exact VG.Proof.Bignum.bytesAt_length _ _ _

end VG.Proof.RsaKeyGen.X86.Candidate
