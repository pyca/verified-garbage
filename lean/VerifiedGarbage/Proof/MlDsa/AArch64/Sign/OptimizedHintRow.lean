module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedResponse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK
public import VerifiedGarbage.Proof.MlDsa.ResponseHintContract
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintDecompose
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowState
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! ## From `OptimizedHintCheck.lean` -/

@[expose] public section

/-! ## From `OptimizedHintRow.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- The response hint is unchanged when low/high decomposition is kept separately. -/
theorem hintRow_value (p : Params) (σ : State) (κ i : Nat) :
    Vector.zipWith (fun ci fi=>makeHint p.γ₂ (-ci) (fi+ci))
      (CT0v p σ κ i) (W'v p σ κ i) = Hv p σ κ i := by
  apply Vector.ext
  intro j hj
  simp only [Hv,VG.Proof.MlDsa.Sign.hF,VG.Proof.MlDsa.Sign.w''F,
    neg,add,Vector.getElem_zipWith,Vector.getElem_map]

end VG.Proof.MlDsa.AArch64.Sign

end
