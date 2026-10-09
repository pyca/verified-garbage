import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitializationTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem PositiveXS.conversion {p : Params} {D : Nat} {σ x : State}
    (h : PositiveXS p D σ x) (h1 : x.gpr .x24=1) :
    ConversionI p D (-(q:Int)+1) ((q:Int)-1) 0 σ x := by
  obtain ⟨t,_,_,_,hpass,hct,hz,hh⟩ := h.pass h1
  exact ⟨p.ℓ*t,⟨⟨⟨h.k.d.im.st,h.k.d.roots⟩,by intro j hj; omega,
    fun j _ hj=>hz j hj,h1⟩,hct,hh⟩,hpass⟩

/-- Initialization, bounded rejection, and accepted-output packing retain the
same observable leakage as the signing contract. -/
theorem positiveRest_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (hp : Ok3 p) {checks : Prog isa}
    (hchecks : ∀σ s t,PositiveIB p D σ t s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u=>PositiveEP p D σ t u ∨ PositiveEF p D σ t u)
    (hct : PositiveChecksCT p D checks) :
    RelCT isa (RootRS p D (LeakEq p 0) fun σ s=>IM p D σ s ∧ StaticRoots D s)
      (Impl.MlDsa.AArch64.Sign.Optimized.restWith keccak.callee P p checks)
      (RootRS p D (LeakEq p 0) (FS p D)) := by
  refine liftRootR (fun _ _ _ h=>positiveRest_ok hP hp hchecks h.1 h.2) ?_
  unfold Impl.MlDsa.AArch64.Sign.Optimized.restWith
  refine RelCT.seq (positiveInitialization_tr hP hp) (RelCT.seq (positiveSignLoop_tr hP hp hct) ?_)
  unfold ifOk
  refine ifOkElse_tr (fun x y h=>by rw [h.2.1])
    (RelCT.mono (optimizedOutput_tr hP hp (lo := -(q:Int)+1) (hi := (q:Int)-1) (by omega) (by omega)
      (E := fun _ _=>True)) ?_ (fun _ _ h=>h))
    (RelCT.mono nil_tr (fun _ _ h=>h) (fun _ _ _=>trivial))
  rintro x y ⟨⟨⟨⟨σ,τ,ps,pt,pub,_,hx,hy⟩,_⟩,eq,hj⟩,hne⟩
  have ex := x24_one hx.r01 hne
  have ey : y.gpr .x24=1 := eq ▸ ex
  obtain ⟨_,f,fx,fy⟩ := hj ex
  exact ⟨⟨σ,τ,ps,pt,pub,trivial,hx.conversion ex,hy.conversion ey⟩,f,fx,fy⟩

end VG.Proof.MlDsa.AArch64.Sign
