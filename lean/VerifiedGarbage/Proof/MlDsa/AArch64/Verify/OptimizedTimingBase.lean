import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa

def RootPair (p : Params) (S : Nat) (I : State → State → Prop) (x y : State) : Prop :=
  VR p S I x y ∧ Sign.RootSymbolsEq x y

theorem rootPair_progress {p : Params} {S : Nat} {I J : State → State → Prop} {c : Prog isa}
    (hw : ∀σ s,vPre p S σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (RootPair p S I) c fun _ _=>True) :
    RelCT isa (RootPair p S I) c (RootPair p S J) := by
  intro x y tx ty u v hr ex ey
  obtain ⟨he,_⟩ := ht _ _ _ _ _ _ hr ex ey
  obtain ⟨⟨σ,τ,hσ,hτ,pub,ix,iy⟩,et⟩ := hr
  obtain ⟨_,u',eu,ju⟩ := hw σ x hσ ix
  obtain ⟨_,v',ev,jv⟩ := hw τ y hτ iy
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  refine ⟨he,⟨σ,τ,hσ,hτ,pub,ju,jv⟩,?_⟩
  simpa only [Sign.RootSymbolsEq,VG.AArch64.Exec.syms eu,VG.AArch64.Exec.syms ev] using et

abbrev SCx (p : Params) (S j : Nat) (cn : Bool) (r : Nat) (σ s : State) : Prop :=
  ∃h A' c0 q, SC p S σ h A' c0 q j cn r s

end VG.Proof.MlDsa.AArch64.Verify.Optimized
