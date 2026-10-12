module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.Sha512.Arm.Stream
meta import VerifiedGarbage.Impl.Sha512.Arm.Stream
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SHA-512 on Arm: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha512.Arm.compress
materialize_code Impl.Sha512.Arm.Stream.update
materialize_code Impl.Sha512.Arm.Stream.finalize

end VG
