module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Checking
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Invoke

import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mont.Words32
/-! The checked domain and canonical table retained across rejection sampling. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/SamplerFrame.lean`, which only this module imported.
section

/-! The rejection sampler writes only its stack frame, preserving the retained comb. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Dsa.X86.KeyRandom
open VG.Impl.Dsa.X86.Comb

theorem samplerFrame {s₀ : State} {m m' : Mem} {rs : List (Nat × Nat)}
    (O : Outs (rBase s₀) rs m m') (fits : ∀ r∈rs, r.1+r.2≤120) :
    Frame [rStack s₀] m m' := by
  refine (O.frame fits).sub ?_
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨rStack s₀,List.mem_singleton_self _,?_⟩
  rw [rBase, rLow_off]
  exact Offset.sub_base (rCall s₀) (d := 88 + 24) (n := 120) (k := 232) (by decide)

theorem sampler_context_kept {s₀ : State} {n e p g : Nat} {m m' : Mem}
    (A : KeyABI s₀) (F : Frame [rStack s₀] m m')
    (fits : context n+8*Proof.Dsa.FixedBaseComb.contextWords (layout n e)≤(arg s₀ 10).toNat*8)
    (C : canonical n e p g (argumentPointer s₀ 9) m) :
    canonical n e p g (argumentPointer s₀ 9) m' := by
  unfold canonical
  rw [VG.Proof.Rsa.wordsAt_frame F (by have := A.scratchBound; omega) (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact A.stackScratchWide.symm.sub_left (Offset.sub_base (argumentPointer s₀ 9)
      (d := context n) (n := 8*Proof.Dsa.FixedBaseComb.contextWords (layout n e))
      (k := (arg s₀ 10).toNat*8) fits))]
  exact C

end VG.Proof.Dsa.X86.Comb
end

end

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
  have layoutSize : context (((arg s 5).toNat+7)/8)+8*Proof.Dsa.FixedBaseComb.contextWords
      (layout (((arg s 5).toNat+7)/8) (((arg s 6).toNat+3)/4))=
      (layout (((arg s 5).toNat+7)/8) (((arg s 6).toNat+3)/4)).size := by
    have sup := supported_widths A.lengths
    rcases sup with ⟨h,e⟩|⟨h,e⟩|⟨h,e⟩|⟨h,e⟩|⟨h,e⟩ <;> rw [h,e] <;> rfl
  rw [layoutSize]
  omega

end VG.Proof.Dsa.X86.Comb
