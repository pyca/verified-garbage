import VerifiedGarbage.Impl.P256.EcdhInverse
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64

theorem inverse_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) Impl.P256.EcdhInverse.inverse :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.EcdhInverse
