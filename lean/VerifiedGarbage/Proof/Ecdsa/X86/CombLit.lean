module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Ecdsa.P256.X86Comb
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86Comb
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG
materialize_code Impl.Ecdsa.X86.signP256Comb
end VG
