module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words32

/-! The rejection sampler writes only its stack frame, preserving the retained comb. -/

@[expose] public section
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
    (fits : context n+8*Spec.Dsa.FixedBaseComb.contextWords (layout n e)≤(arg s₀ 10).toNat*8)
    (C : canonical n e p g (argumentPointer s₀ 9) m) :
    canonical n e p g (argumentPointer s₀ 9) m' := by
  unfold canonical
  rw [VG.Proof.Rsa.wordsAt_frame F (by have := A.scratchBound; omega) (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact A.stackScratchWide.symm.sub_left (Offset.sub_base (argumentPointer s₀ 9)
      (d := context n) (n := 8*Spec.Dsa.FixedBaseComb.contextWords (layout n e))
      (k := (arg s₀ 10).toNat*8) fits))]
  exact C

end VG.Proof.Dsa.X86.Comb
