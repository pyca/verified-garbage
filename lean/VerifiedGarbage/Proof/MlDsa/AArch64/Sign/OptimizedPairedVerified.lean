import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedSignContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedConcreteCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedSignTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedSelectedTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The paired signer satisfies the original algorithm and leakage contract. -/
theorem pairedSign_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : Ok3 p) :
    Verified AArch64.target
      (Impl.MlDsa.AArch64.Sign.Optimized.signWith v.callee (primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (signContract p (abi.withConsts pairedSignRootConsts) signStack) := by
  apply Verified.of_correct (k:=pairedSignK p signStack)
  · intro σ h
    exact selectedPairedSign_correct v hp σ h.1 h.2.1 h.2.2
  · apply pairedSign_ct (keccak:=v) (prims_okWith (keccak:=v)) hp
    · have hd := (Message.pairedInitialization_dle v p).le
      change 16 * _ ≤ 16
      omega
    · have hd := (Message.pairedCommit_dle v hp).le
      change 16 * _ ≤ 16
      omega
    · have hd := (Message.pairedBall_dle v p).le
      change 16 * _ ≤ 16
      omega
    · intro σ s t hi ri h1
      exact positivePairedChecks_ok hp (by rcases hp with rfl|rfl|rfl <;> decide)
        (by decide) (by decide) ri hi h1
    · exact selectedPairedChecks_tr hp
  · exact pairedSignK_implies_spec hp

end VG.Proof.MlDsa.AArch64.Sign
