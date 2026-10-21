module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Checking
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Invoke
import VerifiedGarbage.Proof.Dsa.X86.Comb.SamplerFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower

/-! The checked domain and canonical table retained across rejection sampling. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

/-- Include the caller's resource evidence so arbitrary sampler writes can be
shown disjoint from this context. -/
def keyInvariant (s : State) (mem : Mem) : Prop :=
  KeyABI s ∧ parameterContext (argumentPointer s 9) (arg s 5).toNat (arg s 6).toNat (rInput s).key mem

theorem keyInvariant_stable : StableScratch keyInvariant := by
  intro s m m' rs O fits ⟨A,C⟩
  refine ⟨A,?_⟩
  unfold parameterContext at C ⊢
  apply sampler_context_kept A (samplerFrame O fits) ?_ C
  have S := context_fits A.lengths
  have Gen := A.scratchLength
  unfold Spec.Dsa.generationScratchWords at Gen
  unfold Spec.Dsa.scratchWords at S
  have layoutSize : context (((arg s 5).toNat+7)/8)+8*Spec.Dsa.FixedBaseComb.contextWords
      (layout (((arg s 5).toNat+7)/8) (((arg s 6).toNat+3)/4))=
      (layout (((arg s 5).toNat+7)/8) (((arg s 6).toNat+3)/4)).size := by
    have sup := supported_widths A.lengths
    rcases sup with ⟨h,e⟩|⟨h,e⟩|⟨h,e⟩|⟨h,e⟩|⟨h,e⟩ <;> rw [h,e] <;> rfl
  rw [layoutSize]
  omega

end VG.Proof.Dsa.X86.Comb
