import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa

theorem liftPairedForgetR {p : Params} {S : Nat} {E I J : State → State → Prop} {code : Prog isa}
    (hw : ∀σ s,(signK p S).pre σ → I σ s → PairedRoots S s → WP isa code s (J σ))
    (ht : RelCT isa (PairedRS p S E I) code fun _ _=>True) :
    RelCT isa (PairedRS p S E I) code (RootRS p S E J) := by
  intro x y tx ty x' y' h ex ey
  have heq := (ht _ _ _ _ _ _ h ex ey).1
  obtain ⟨σ,τ,ps,pt,pub,he,hx,hy⟩ := h.1.1
  obtain ⟨_,u,eu,hu⟩ := hw σ x ps hx.1 hx.2
  obtain ⟨_,v,ev,hv⟩ := hw τ y pt hy.1 hy.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨heq,⟨σ,τ,ps,pt,pub,he,hu,hv⟩,by
    simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using h.1.2⟩

end VG.Proof.MlDsa.AArch64.Sign
