module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryHash
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryPrime
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructPlan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.BufferSeparate
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
public import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PConstruct
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArguments
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateFromFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateReduction
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Double
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyArgs
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawPrepared
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashSequence
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashShape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashValue
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Increment
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopExhausted
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopRound
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuild
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeArgs
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeArguments
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeReject
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTapeCheck
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeEnds
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Reduce
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReduceFromFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReductionExponent
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundHeader
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subtract
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceBase
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceWords
public import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
public import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PConstruct
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateFromFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Double
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawPrepared
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashSequence
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashValue
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Increment
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopExhausted
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopRound
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuild
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoop
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeReject
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTapeCheck
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeEnds
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReduceFromFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReductionExponent
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subtract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceWords
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Dsa.Generation.Trial

/-! # Concrete p-candidate construction plan for each accepted subgroup candidate -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.constructPlan (p : GenerationGeometry) (seed : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64) (offset : Nat)
    (carry : offset + p.count < 2 ^ 32)
    (h1 : W 1 = seed.ptr) (h3 : W 3 = VG.Proof.Bignum.off p.B wrappedSeed)
    (h4 : W 4 = VG.Proof.Bignum.off p.B hashes) (h2 : W 2 = BitVec.ofNat 64 offset)
    (h5 : W 5 = p.B) (h0 : W 0 = VG.Proof.Bignum.off p.B shaped) : PConstructPlan := by
  let N := Spec.Dsa.qCandidate (8 * p.qLen) seed.bytes
  have qshape := VG.Proof.Dsa.Generation.qCandidate_shape
    (show 2 ≤ 8 * p.qLen by rcases p.qWidth with h | h <;> omega) seed.bytes
  have qfit : N < 256 ^ p.qLen := by
    change N < (2 ^ 8) ^ p.qLen
    rw [← Nat.pow_mul]
    exact qshape.2.2
  have qdecode : Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.qLen N) = N := VG.Proof.Dsa.decodeBE_encodeBE qfit
  have ha : arithmetic + arithmeticBytes ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hs : shaped + p.pLen ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hp : VG.Impl.Dsa.Generation.Layout.p + p.pLen ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have he : exponent + p.pLen ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hq : q + p.qLen ≤ usedBytes p.pLen := by
    rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
  have hh : VG.Impl.Dsa.Generation.Layout.hash + oRsa ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hhash : hashes + (p.count + 1) * p.qLen ≤ usedBytes p.pLen := by
    have hn := p.hashSizes.2.1
    rcases p.width with h | h | h <;> rw [h] <;> unfold hashes usedBytes domainCheck <;> omega
  have hw : wrappedSeed + p.qLen ≤ usedBytes p.pLen := by
    rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  refine {
    hash := p.hashPlan seed seedLength W offset carry h1 h3 h4 h2
    B := VG.Proof.Bignum.off p.B arithmetic
    Z := arithmeticBytes
    len := p.pLen
    qb := Spec.Dsa.encodeBE p.qLen N
    width := p.width
    base := by change W 5 + _ = _; rw [h5]
    workspaceRoom := by rcases p.width with h | h | h <;> rw [h] <;> decide
    qLength := VG.Proof.Dsa.encodeBE_length _ _
    qPositive := by rw [qdecode]; exact Nat.lt_of_lt_of_le (by decide) (p.qShape seed.bytes).2
    qFits := by
      rw [qdecode]
      apply Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left qfit (by decide : 0 < 2))
      change 2 * (2 ^ 8) ^ p.qLen ≤ 2 ^ (64 * (p.pLen / 8))
      rw [← Nat.pow_mul, ← Nat.pow_succ']
      apply Nat.pow_le_pow_right (by decide)
      rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
    hashCount := rfl
    hashRoom := p.hashSizes.2.2
    shapedSlot := by change W 0 = VG.Proof.Bignum.off (W 5) shaped; rw [h5]; exact h0
    shapedOutside := ?_
    shapedHash := ?_
    shapedInput := ?_
    frameHeaders := p.frame_headers
    frameOutside := p.frame_outside
    qHash := ?_
    pOutside := ?_
    exponentOutside := ?_
    pExponent := ?_
    frameArithmetic := ?_
    hashArithmetic := ?_ }
  · change ∀ i < p.pLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) shaped) i)
    rw [h5]
    intro i hi
    exact out_scr (p.parts_disjoint hs ha (Or.inl (by unfold shaped arithmetic; omega)))
      (Offset.contains_base _ (by omega) (by omega))
  · change HashBufferSeparate p.F p.hash (VG.Proof.Bignum.off (W 5) shaped) p.pLen
    rw [h5]
    exact bufferSeparate_of_regions (by omega) (p.frame_part hs).symm
      (p.parts_disjoint hs hh (Or.inr (by decide)))
  · change ∀ i < p.pLen, ∀ j < p.pLen,
      VG.Proof.Bignum.off (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B hashes) ((p.count + 1) * p.qLen - p.pLen)) i ≠ VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) shaped) j
    rw [h5]
    intro i hi j hj eq
    have dis := p.parts_disjoint hhash hs (Or.inl (by
      have := p.hashSizes.2.1; unfold hashes shaped; omega))
    apply dis (VG.Proof.Bignum.off (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B hashes) ((p.count + 1) * p.qLen - p.pLen)) i)
    · rw [VG.Proof.Bignum.off_off]
      exact Offset.contains_base _ (by omega_using [p.hashSizes.2.2, hi]) (by omega_using [p.hashSizes.2.1, p.hashSizes.2.2, hi])
    · rw [eq]
      exact Offset.contains_base _ (by omega) (by omega)
  · change ∀ r ∈ ⟨VG.Proof.Bignum.off (W 5) shaped, p.pLen⟩ ::
      [⟨VG.Proof.Bignum.off p.B hashes, (p.count + 1) * p.qLen⟩, ⟨VG.Proof.Bignum.off p.B wrappedSeed, p.qLen⟩, ⟨p.hash, oRsa⟩, retR p.F],
      (⟨VG.Proof.Bignum.off (W 5) q, (Spec.Dsa.encodeBE p.qLen N).length⟩ : Region).Disjoint r
    rw [h5, VG.Proof.Dsa.encodeBE_length]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact p.parts_disjoint hq hs (Or.inr (by unfold shaped q; omega))
    · exact p.parts_disjoint hq hhash (Or.inr (by have := p.hashSizes.2.1; unfold hashes q; omega))
    · exact p.parts_disjoint hq hw (Or.inr (by unfold wrappedSeed q; omega))
    · exact p.parts_disjoint hq hh (Or.inr (by decide))
    · exact (p.stack_part hq).symm.sub_right (below_sub (by decide) (by decide))
  · change ∀ i < p.pLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p) i)
    rw [h5]
    intro i hi
    exact out_scr (p.parts_disjoint hp ha (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p arithmetic; omega)))
      (Offset.contains_base _ (by omega) (by omega))
  · change ∀ i < p.pLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) i)
    rw [h5]
    intro i hi
    exact out_scr (p.parts_disjoint he ha (Or.inl (by unfold exponent arithmetic; omega)))
      (Offset.contains_base _ (by omega) (by omega))
  · change ∀ i < p.pLen, ∀ j < p.pLen, VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p) i ≠ VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) j
    rw [h5]
    intro i hi j hj eq
    apply (p.parts_disjoint hp he (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p exponent; omega))) (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B VG.Impl.Dsa.Generation.Layout.p) i)
      (Offset.contains_base _ (by omega) (by omega))
    rw [eq]
    exact Offset.contains_base _ (by omega) (by omega)
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩, ⟨VG.Proof.Bignum.off (W 5) exponent, p.pLen⟩],
      (⟨p.F, frameBytes⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.frame_part ha
    · exact p.frame_part hp
    · exact p.frame_part he
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩, ⟨VG.Proof.Bignum.off (W 5) exponent, p.pLen⟩],
      (⟨p.hash, oRsa⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.parts_disjoint hh ha (Or.inl (by decide))
    · exact p.parts_disjoint hh hp (Or.inl (by decide))
    · exact p.parts_disjoint hh he (Or.inl (by decide))

end VG.Proof.Dsa.AArch64.Generation
