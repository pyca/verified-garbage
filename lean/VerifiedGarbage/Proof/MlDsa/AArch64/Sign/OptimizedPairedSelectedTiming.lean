import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedDepth

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem selectedPairedChecks_tr {p : Params} (hp : Ok3 p) :
    PairedChecksCT p 16 (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) := by
  intro t ht
  apply positivePairedChecks_tr hp (by rcases hp with rfl|rfl|rfl <;> decide) (by decide) (by decide)
  intro σ τ he hs ht'
  exact leq_pass (paramsOk hp) he ht hs ht'

theorem selectedPairedSignLoop_tr (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : Ok3 p) :
    RelCT isa (PairedRS p 16 (LeakEq p 0) (PositiveIK p 16))
      (Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith v.callee (primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) (PositiveOX p 16) := by
  apply pairedSignLoop_tr (keccak:=v) (prims_okWith (keccak:=v)) hp (selectedPairedChecks_tr hp)
  · have hd := (Message.pairedCommit_dle v hp).le
    change 16 * _ ≤ 16
    omega
  · have hd := (Message.pairedBall_dle v p).le
    change 16 * _ ≤ 16
    omega

end VG.Proof.MlDsa.AArch64.Sign
