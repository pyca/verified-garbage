import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa

theorem PairedRS.of_root {p : Params} {S : Nat} {E I : State → State → Prop} {x y : State}
    (h : RootRS p S E I x y) (rx : PairedRoots S x) (ry : PairedRoots S y)
    (he : x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR") : PairedRS p S E I x y := by
  obtain ⟨⟨σ,τ,ps,pt,pub,e,hx,hy⟩,roots⟩ := h
  exact ⟨⟨⟨σ,τ,ps,pt,pub,e,⟨hx,rx⟩,⟨hy,ry⟩⟩,roots⟩,he⟩

/-- Preserve the immutable paired table while retaining an arbitrary relational postcondition. -/
theorem paired_trace_frame {p : Params} {S : Nat} {E I Q : State → State → Prop}
    {code : Prog isa} (hd : 16*code.aarch64Depth≤S) (hS : S<2^64)
    (ht : RelCT isa (RootRS p S E I) code Q) :
    RelCT isa (PairedRS p S E I) code fun x y=>Q x y ∧ PairedRoots S x ∧ PairedRoots S y ∧
      x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR" := by
  intro x y tx ty x' y' h ex ey
  have res := ht _ _ _ _ _ _ h.root ex ey
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1.1
  exact ⟨res.1,res.2,hx.2.exec ex hd hS,hy.2.exec ey hd hS,by
    simpa only [VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using h.2⟩

end VG.Proof.MlDsa.AArch64.Sign
