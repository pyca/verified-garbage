module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedDepth

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem selectedPairedChecks_tr {p : Params} (hp : Ok3 p) :
    PairedChecksCT p 16 (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) := by
  intro t ht
  apply positivePairedChecks_tr hp (by rcases hp with rfl|rfl|rfl <;> decide) (by decide) (by decide)
  intro σ τ he hs ht'
  exact leq_prefixAgree (paramsOk hp) he ht hs ht'

end VG.Proof.MlDsa.AArch64.Sign
