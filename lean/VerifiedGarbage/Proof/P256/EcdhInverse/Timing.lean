module

public import VerifiedGarbage.Impl.P256.EcdhInverse
meta import VerifiedGarbage.Impl.P256.EcdhInverse
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64

theorem inverse_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) Impl.P256.EcdhInverse.inverse :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.EcdhInverse
