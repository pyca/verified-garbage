module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryPrime
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BufferSeparate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BufferSeparate
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
public import VerifiedGarbage.Proof.Dsa.Generation.Trial
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopExhausted
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopInit
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopRound
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopStep
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeArguments
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFootprint
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFromFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeReject
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeResult
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QShape
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Trial
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
public import VerifiedGarbage.Proof.Dsa.X86_64.Setup
public import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LowByte
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
public import VerifiedGarbage.Proof.Rsa.X86_64.Inv
public import VerifiedGarbage.Proof.Rsa.X86_64.Loops
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopExhausted
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopInit
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopRound
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopStep
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeArguments
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFootprint
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFromFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeReject
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeResult
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QShape
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Trial
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LowByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! # Concrete q-phase layout inside the shared generation arena -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.subgroupPlan (p : GenerationGeometry) (rand seed : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64)
    (h5 : W 5 = p.B) (h0 : W 0 = off p.B q)
    (h13 : W 13 = rand.ptr) (h15 : W 15 = BitVec.ofNat 64 rand.bytes.length) : SubgroupPlan := by
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
    hash := p.hash
    seedPtr := seed.ptr
    output := off p.B q
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
    tapePtr := h13
    tapeLength := h15
    frameHeaders := p.frame_headers
    frameOutside := p.frame_outside
    outputOutside := by
      change ∀ i < p.qLen, arithmeticBytes ≤ ofs (off p.B arithmetic) (off (off p.B q) i)
      intro i hi
      exact out_scr hqa (Offset.contains_base _ (by omega) (by rcases p.qWidth with h | h <;> omega))
    outputFrame := (p.frame_part hq).symm
    outputHash := bufferSeparate_of_regions (len := p.qLen) (by rcases p.qWidth with h | h <;> omega) (p.frame_part hq).symm hqh
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
      rcases hr with rfl | rfl | rfl
      · exact p.frame_part ha
      · exact p.frame_part hw
      · exact p.frame_below
    hashPrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact p.parts_disjoint hh ha (Or.inl (by decide))
      · exact p.parts_disjoint hh hw (Or.inl (by decide))
      · exact (p.stack_part hh).symm
    outputPrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hqa
      · exact hqw
      · exact (p.stack_part hq).symm }

end VG.Proof.Dsa.X86_64.Generation
