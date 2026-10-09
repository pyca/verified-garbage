import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedTimingBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots)
open VG.Proof.MlDsa.AArch64.Verify.Optimized (RootPair rootPair_progress)

/-- A bounded phase retains the immutable transform roots without making
any sampled coefficients or SHAKE states public. -/
theorem rooted_piece {p : Params} {S : Nat} {I J : State→State→Prop} {c : Prog isa}
    (h : VPiece p S I J c) (hd : 16*c.aarch64Depth≤S) (hS : S<2^64) :
    VPiece p S (fun σ s=>I σ s ∧ StaticRoots S s) (fun σ s=>J σ s ∧ StaticRoots S s) c := by
  refine ⟨fun σ s hp hs=>hs.2.phase hd hS (h.ok σ s hp hs.1),?_⟩
  exact RelCT.mono h.tr
    (fun _ _ ⟨σ,τ,hσ,hτ,pub,ix,iy⟩=>⟨σ,τ,hσ,hτ,pub,ix.1,iy.1⟩)
    (fun _ _ _=>trivial)

/-- Sampling preserves both root tables while retaining the existing exact
success/failure and rejection-transcript semantics. -/
theorem samples_rooted_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S)
    {p : Params} (hF : VFacts p) :
    VPiece p S
      (fun σ s=>(Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) ∧ StaticRoots S s)
      (fun σ s=>VB p σ s ∧ StaticRoots S s)
      (Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p) :=
  rooted_piece (samples_vpiece hP hF) (samples_depth hP p) hP.s64

/-- The paired timing relation also preserves the shared table addresses. -/
theorem samples_rootPair {P : Prims} {S : Nat} (hP : PrimsOk P S)
    {p : Params} (hF : VFacts p) :
    RelCT isa
      (RootPair p S (fun σ s=>(Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) ∧ StaticRoots S s))
      (Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p)
      (RootPair p S (fun σ s=>VB p σ s ∧ StaticRoots S s)) := by
  have h := samples_rooted_vpiece hP hF
  exact rootPair_progress h.ok
    (RelCT.mono h.tr (fun _ _ hp=>hp.1) (fun _ _ _=>trivial))

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
