import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedDepth

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem selectedPairedSign_correct (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : Ok3 p) (σ : State) (hpre : (signK p 16).pre σ)
    (hr : StaticRoots 16 σ) (rp : PairedRoots 16 σ) :
    ∃t s',Exec isa (Impl.MlDsa.AArch64.Sign.Optimized.signWith v.callee (primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) σ t s' ∧
      abiPreserved σ s' ∧ (signK p 16).post σ s' := by
  apply pairedSign_correct (keccak:=v) (prims_okWith (keccak:=v)) hp σ hpre hr rp
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

end VG.Proof.MlDsa.AArch64.Sign
