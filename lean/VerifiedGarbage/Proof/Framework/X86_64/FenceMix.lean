module

public import VerifiedGarbage.Proof.Framework.FenceMix
import VerifiedGarbage.Proof.Framework.X86_64.Fence
public import VerifiedGarbage.Proof.Framework.X86_64.Spectre
public import VerifiedGarbage.Proof.Framework.Fence
public import VerifiedGarbage.TCB.X86_64.Target

/-!
# Fences where they are needed, on x86-64

Each verified x86-64 artifact is speculatively safe in one of two forms:

* `verified_fenceFn_safe`: with `lfence` at its entry and every branch
  target (any artifact, however its constant time was proven; for every
  transient semantics in which `lfence` is a barrier);
* `verified_taint_safe`: with only an `lfence` before it returns, when the
  taint analysis checks it (for the transient semantics `spectre`, for which
  the analysis is sound, `Spectre.specSound`).
-/

@[expose] public section

namespace VG.X86_64

theorem verified_fenceFn_safe {c : Prog isa} {k : Contract isa} (h : Verified target c k)
    {S : Spectre isa} (hf : S.fence .lfence = true) :
    Verified target (c.fenceFn .lfence) k ∧ SpecSafe S k.pre k.pub (c.fenceFn .lfence) :=
  ⟨h.fenceIns lfence_nop (.fenceFn _ _),
    specSafe_fenceFn leakShape lfence_nop hf (fun s hs => let ⟨t, s', e, _⟩ := h.1 s hs; ⟨t, s', e⟩)
      h.2.1⟩

theorem verified_taint_safe {c : Prog isa} {k : Contract isa} (h : Verified target c k)
    (τ : Taint.T) (hpub : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Taint.Agree τ s₁ s₂)
    {hc : VG.Taint.Hint Taint.T}
    (hk : (taint.check τ (.seq c (.block [.lfence])) hc).isSome = true) :
    Verified target (.seq c (.block [.lfence])) k ∧
      SpecSafe Spectre.spectre k.pre k.pub (.seq c (.block [.lfence])) :=
  ⟨h.fenceIns lfence_nop (.post (.refl _)), specSafe_taint Spectre.specSound rfl τ hpub hk⟩

end VG.X86_64
