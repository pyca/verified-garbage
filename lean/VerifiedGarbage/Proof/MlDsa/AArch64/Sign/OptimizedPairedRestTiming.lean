import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsForget
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitializationTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

/-- Initialization, bounded rejection, and accepted-output packing retain the
same observable leakage as the signing contract. -/
theorem pairedRest_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (hp : Ok3 p) {checks : Prog isa}
    (hinit : 16*(positiveDecodeWith keccak.callee P p).aarch64Depth≤D)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤D)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤D)
    (hchecks : ∀σ s t,PositiveIB p D σ t s → PairedRoots D s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u=>(PositiveEP p D σ t u ∨ PositiveEF p D σ t u) ∧ PairedRoots D u)
    (hct : PairedChecksCT p D checks) :
    RelCT isa (PairedRS p D (LeakEq p 0) fun σ s=>IM p D σ s ∧ StaticRoots D s)
      (Impl.MlDsa.AArch64.Sign.Optimized.restWith keccak.callee P p checks)
      (RootRS p D (LeakEq p 0) (FS p D)) := by
  refine liftPairedForgetR (fun _ _ _ h rp=>pairedRest_ok hP hp hinit hcommit hball hchecks h.1 h.2 rp) ?_
  unfold Impl.MlDsa.AArch64.Sign.Optimized.restWith
  have hi := RelCT.mono (paired_trace_frame hinit hP.s64 (positiveInitialization_tr (E:=LeakEq p 0) hP hp))
    (fun _ _ h=>h) (fun _ _ h=>PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2)
  refine RelCT.seq hi (RelCT.seq (pairedSignLoop_tr hP hp hct hcommit hball) ?_)
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
