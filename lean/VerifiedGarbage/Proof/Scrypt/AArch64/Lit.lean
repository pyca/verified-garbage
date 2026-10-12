module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix
meta import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# scrypt on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Scrypt.AArch64.salsa
materialize_code Impl.Scrypt.AArch64.blockMix
materialize_code Impl.Scrypt.AArch64.roMix

end VG
