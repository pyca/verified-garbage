module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryPrime
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SubgroupState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.BufferSeparate
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Subgroup
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateReduction
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Double
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyArgs
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawPrepared
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Increment
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopExhausted
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopRound
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeArguments
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFootprint
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeReject
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeResult
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTapeCheck
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QArgs
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QCandidate
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeEnds
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Reduce
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReductionExponent
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundHeader
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subtract
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceBase
public import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
public import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Subgroup
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.BufferSeparate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Double
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawPrepared
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Increment
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopExhausted
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopRound
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFootprint
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoop
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeReject
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeResult
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTapeCheck
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeEnds
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReductionExponent
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subtract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Dsa.Generation.Trial

/-! # Concrete q-phase layout inside the shared generation arena -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.subgroupPlan (p : GenerationGeometry) (rand seed : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64)
    (h5 : W 5 = p.B) (h0 : W 0 = VG.Proof.Bignum.off p.B q)
    (h14 : W 14 = rand.ptr) (h15 : W 15 = BitVec.ofNat 64 rand.bytes.length) : SubgroupPlan := by
  have ha : arithmetic + arithmeticBytes ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hh : VG.Impl.Dsa.Generation.Layout.hash + oRsa ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hq : q + p.qLen ≤ usedBytes p.pLen := by
    rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
  have hw : witness + p.qLen ≤ usedBytes p.pLen := by
    rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
  have hqa : (p.part q p.qLen).Disjoint (p.part arithmetic arithmeticBytes) :=
    p.parts_disjoint hq ha (by left; rcases p.qWidth with h | h <;> rw [h] <;> decide)
  have hqh : (p.part q p.qLen).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.hash oRsa) :=
    p.parts_disjoint hq hh (Or.inr (by decide))
  have hqw : (p.part q p.qLen).Disjoint (p.part witness p.qLen) :=
    p.parts_disjoint hq hw (by left; rcases p.qWidth with h | h <;> rw [h] <;> decide)
  exact {
    prime := p.qPrime rand seed.bytes
    F := p.F
    hash := p.hash
    seedPtr := seed.ptr
    output := VG.Proof.Bignum.off p.B q
    seed := seed.bytes
    W := W
    width := p.qWidth
    words := rfl
    size := rfl
    draw := rfl
    checks := rfl
    seedLength := seedLength
    modulus := rfl
    base := by change W 5 + _ = _; rw [h5]; rfl
    outputPtr := by change W 5 + _ = _; rw [h5]
    outputSlot := h0
    witnessPtr := by change W 5 + _ = _; rw [h5]; rfl
    tapePtr := h14
    tapeLength := h15
    frameHeaders := p.frame_headers
    frameOutside := p.frame_outside
    outputOutside := by
      change ∀ i < p.qLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B q) i)
      intro i hi
      exact out_scr hqa (Offset.contains_base _ (by omega) (by rcases p.qWidth with h | h <;> omega))
    outputFrame := (p.frame_part hq).symm
    outputScratch := hqh.symm
    tapeHash := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rand.part hq
      · exact rand.part hh
      · exact rand.stack.sub_right (below_sub (by decide) (by decide))
    framePrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact p.frame_part ha
      · exact p.frame_part hw
    hashPrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact p.parts_disjoint hh ha (Or.inl (by decide))
      · exact p.parts_disjoint hh hw (Or.inl (by decide))
    outputPrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hqa
      · exact hqw
      }

end VG.Proof.Dsa.AArch64.Generation
