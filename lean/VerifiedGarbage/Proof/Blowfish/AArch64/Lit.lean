module

public import VerifiedGarbage.Impl.Blowfish.AArch64
meta import VerifiedGarbage.Impl.Blowfish.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.AArch64.encrypt
materialize_code Impl.Blowfish.AArch64.decrypt
materialize_code Impl.Blowfish.AArch64.expandKey

end VG
