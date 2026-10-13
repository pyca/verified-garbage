module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.Scrypt.Arm.RoMix
meta import VerifiedGarbage.Impl.Scrypt.Arm.RoMix
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# scrypt on Arm: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Scrypt.Arm.salsa
materialize_code Impl.Scrypt.Arm.blockMix
materialize_code Impl.Scrypt.Arm.roMix

end VG
