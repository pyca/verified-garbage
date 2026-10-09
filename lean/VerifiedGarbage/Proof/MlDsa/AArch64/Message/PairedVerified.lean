import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedTopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedSat
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedArtifactDepth

namespace VG.Proof.MlDsa.AArch64.Message.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Sign (pairedSignRootConsts)

/-- The message wrapper retains the public signing API and immutable tables
required by its verified optimized signing callee. -/
theorem signMessage_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p∈params) :
    Verified target (signMessage v.callee n c p)
      (signMessageContract p (abi.withConsts pairedSignRootConsts) 16) :=
  ⟨fun _ h=>let ⟨t,s',he,ha,hq⟩ := signMessage_wp v hS hp h; ⟨t,s',he,ha,hq⟩,
    signMessage_ct v hS hp,⟨signSat p,sign_sat (params3 hp)⟩⟩

/-- The optimized signer is an admissible callee, including the same stack
bound and all immutable-root requirements. -/
theorem signFn (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : p∈params) :
    SignFn p (Impl.MlDsa.AArch64.Sign.Optimized.signWith v.callee (Sign.primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) :=
  ⟨Sign.pairedSign_verified v (params3 hp),pairedSignWith_dle v (params3 hp)⟩

end VG.Proof.MlDsa.AArch64.Message.Paired
