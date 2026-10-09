import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ball

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3

taint_summary firstSponge : VectorTaint.taint (VectorTaint.ofRegs [.x25,.x26,.x27,.x3,.x4])
  (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 136)
  using Sha3Sums.absorb Sha3Sums.pad Sha3Sums.squeeze

end VG.Proof.MlDsa.AArch64.Optimized.Ball
