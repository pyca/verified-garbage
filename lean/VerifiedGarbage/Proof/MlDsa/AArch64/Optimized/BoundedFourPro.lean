import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSamplerState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64

theorem samplerPro_ok {σ : State} (hp : SamplerPre σ) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.pro) σ (SamplerEnv σ) :=
  ResidentRej.pro_with 4 (fun _ _ h=>sampler_in_work hp rfl h)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
