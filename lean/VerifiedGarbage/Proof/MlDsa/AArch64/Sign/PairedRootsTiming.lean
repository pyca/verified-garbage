import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa

/-- Paired checks add one immutable public table to the existing relation. -/
def PairedRS (p : Params) (S : Nat) (E I : State → State → Prop) (x y : State) : Prop :=
  RootRS p S E (fun σ s => I σ s ∧ PairedRoots S s) x y ∧
    x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR"

theorem PairedRS.mono {p : Params} {S : Nat} {E I J : State → State → Prop} {x y : State}
    (h : PairedRS p S E I x y) (hi : ∀σ s,I σ s → J σ s) : PairedRS p S E J x y :=
  ⟨h.1.mono (fun σ s h => ⟨hi σ s h.1,h.2⟩),h.2⟩

theorem PairedRS.root {p : Params} {S : Nat} {E I : State → State → Prop} {x y : State}
    (h : PairedRS p S E I x y) : RootRS p S E I x y :=
  h.1.mono (fun _ _ h => h.1)

theorem liftPairedR {p : Params} {S : Nat} {E I J : State → State → Prop} {code : Prog isa}
    (hw : ∀ σ s,(signK p S).pre σ → I σ s → PairedRoots S s →
      WP isa code s (fun u => J σ u ∧ PairedRoots S u))
    (ht : RelCT isa (PairedRS p S E I) code fun _ _ => True) :
    RelCT isa (PairedRS p S E I) code (PairedRS p S E J) := by
  intro x y tx ty x' y' h ex ey
  have heq := (ht _ _ _ _ _ _ h ex ey).1
  obtain ⟨σ,τ,hσ,hτ,hpub,he,hx,hy⟩ := h.1.1
  obtain ⟨_,u,eu,hu⟩ := hw σ x hσ hx.1 hx.2
  obtain ⟨_,v,ev,hv⟩ := hw τ y hτ hy.1 hy.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  refine ⟨heq,⟨⟨σ,τ,hσ,hτ,hpub,he,hu,hv⟩,?_⟩,?_⟩
  · simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using h.1.2
  · simpa only [VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using h.2

end VG.Proof.MlDsa.AArch64.Sign
