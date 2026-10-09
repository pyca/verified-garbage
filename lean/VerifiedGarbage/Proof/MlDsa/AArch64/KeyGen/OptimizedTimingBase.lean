import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedEntry

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64
open VG.Spec.MlDsa (Params)

/-- Immutable table addresses are public, while every polynomial value keeps
its original secrecy classification. -/
def TableEq (x y : State) : Prop :=
  x.syms "VG_MLDSA_NTT_EXPANDED"=y.syms "VG_MLDSA_NTT_EXPANDED" ∧
  x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED"

def RootPair (p : Params) (S : Nat) (I : State → State → Prop) (x y : State) : Prop :=
  R p S (fun σ s => I σ s ∧ Sign.StaticRoots S s) x y ∧ TableEq x y

/-- Lift functional progress into the timing invariant without revealing any
additional input value. Symbol maps are preserved by execution semantics. -/
theorem rootPair_progress {p : Params} {S : Nat} {I J : State → State → Prop} {c : Prog isa}
    (hw : ∀σ s,kgPre p S σ → I σ s → Sign.StaticRoots S s →
      WP isa c s fun t => J σ t ∧ Sign.StaticRoots S t)
    (ht : RelCT isa (RootPair p S I) c fun _ _ => True) :
    RelCT isa (RootPair p S I) c (RootPair p S J) := by
  intro x y tx ty u v hr ex ey
  obtain ⟨he,_⟩ := ht _ _ _ _ _ _ hr ex ey
  obtain ⟨⟨σ,τ,hσ,hτ,pub,ix,iy⟩,et⟩ := hr
  obtain ⟨_,u',eu,ju⟩ := hw σ x hσ ix.1 ix.2
  obtain ⟨_,v',ev,jv⟩ := hw τ y hτ iy.1 iy.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  refine ⟨he,⟨σ,τ,hσ,hτ,pub,ju,jv⟩,?_⟩
  simpa only [TableEq,VG.AArch64.Exec.syms eu,VG.AArch64.Exec.syms ev] using et

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
