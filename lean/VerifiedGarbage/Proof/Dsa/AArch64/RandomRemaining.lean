module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawResult
public import VerifiedGarbage.Proof.Dsa.RandomResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomEncoding

/-! Relating a tape offset to the recursive sampling specification. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Proof.Dsa.Random

def randomRemaining (C : RandomContext) (used fuel : Nat) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (Spec.Dsa.decodeBE C.qBytes) fuel (C.rand.drop used)

structure RandomResultRel (C : RandomContext) (start : Nat) (result : Spec.Dsa.Random.Sample)
    (used fuel : Nat) : Prop where
  scalar : result.scalar = (randomRemaining C used fuel).scalar
  consumption : start + result.used = used + (randomRemaining C used fuel).used
  status : sampleStatus result = sampleStatus (randomRemaining C used fuel)

def RandomSamplePost (C : RandomContext) (start : Nat) (result : Spec.Dsa.Random.Sample) (s : State) : Prop :=
  (∃ draws, RandomReady C (start + result.used) draws s) ∧
  word s.mem C.B Random.oStatus = BitVec.ofNat 64 (sampleStatus result) ∧
  ∀ k, result.scalar = some k → RandomNonceValue C k s

theorem random_remaining_short {C : RandomContext} {used fuel : Nat}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes)
    (hshort : C.rand.length - used < (VG.Proof.Dsa.significant C.qBytes).1) :
    randomRemaining C used (fuel + 1) = ⟨none, 0, [2]⟩ := by
  apply sample_short _ _ _ hq
  rwa [List.length_drop, VG.Proof.Dsa.random_drawBytes_scan]

theorem random_remaining_accept {C : RandomContext} {used fuel : Nat}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length)
    (hk : 0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes) :
    randomRemaining C used (fuel + 1) =
      ⟨some (randomNextCandidate C used), (VG.Proof.Dsa.significant C.qBytes).1, [1]⟩ := by
  have hs : Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes) ≤ (C.rand.drop used).length := by
    rw [VG.Proof.Dsa.random_drawBytes_scan, List.length_drop]; omega
  have hk' : 0 < Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
      ((C.rand.drop used).take (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes))) ∧
      Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
      ((C.rand.drop used).take (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes))) < Spec.Dsa.decodeBE C.qBytes := by
    rw [VG.Proof.Dsa.random_drawBytes_scan]; exact hk
  simpa only [randomRemaining, randomNextCandidate, VG.Proof.Dsa.random_drawBytes_scan] using
    sample_accept _ fuel _ hq hs hk'

theorem random_remaining_reject {C : RandomContext} {used fuel : Nat}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length)
    (hk : ¬ (0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes)) :
    randomRemaining C used (fuel + 1) =
      let next := randomRemaining C (used + (VG.Proof.Dsa.significant C.qBytes).1) fuel
      ⟨next.scalar, (VG.Proof.Dsa.significant C.qBytes).1 + next.used, 0 :: next.trace⟩ := by
  have hs : Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes) ≤ (C.rand.drop used).length := by
    rw [VG.Proof.Dsa.random_drawBytes_scan, List.length_drop]; omega
  have hk' : ¬ (0 < Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
      ((C.rand.drop used).take (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes))) ∧
      Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
      ((C.rand.drop used).take (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes))) < Spec.Dsa.decodeBE C.qBytes) := by
    rw [VG.Proof.Dsa.random_drawBytes_scan]; exact hk
  simpa only [randomRemaining, VG.Proof.Dsa.random_drawBytes_scan, List.drop_drop] using
    sample_reject _ fuel _ hq hs hk'

theorem RandomResultRel.reject {C : RandomContext} {start used fuel : Nat} {result : Spec.Dsa.Random.Sample}
    (hr : RandomResultRel C start result used (fuel + 1))
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length)
    (hk : ¬ (0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes)) :
    RandomResultRel C start result (used + (VG.Proof.Dsa.significant C.qBytes).1) fuel := by
  have he := random_remaining_reject hq hfull hk (fuel := fuel)
  refine ⟨?_, ?_, ?_⟩
  · rw [hr.scalar, he]
  · have hu := hr.consumption
    rw [he] at hu
    simp only at hu
    omega
  · rw [hr.status, he]
    exact sampleStatus_reject _ _ _ _

end VG.Proof.Dsa.AArch64
