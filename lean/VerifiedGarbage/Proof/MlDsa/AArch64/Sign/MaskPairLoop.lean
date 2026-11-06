module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairStep

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa

def masksPairChk (p : Params) : Bool :=
  (List.range (p.ℓ/2)).all (fun j => maskPairStepChk p (2*j)) &&
  (List.range p.ℓ).all (mChk p)

end VG.Proof.MlDsa.AArch64.Sign
