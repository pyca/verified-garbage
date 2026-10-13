module

public import VerifiedGarbage.Impl.Blowfish.X86_64
meta import VerifiedGarbage.Impl.Blowfish.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.X86_64.encrypt
materialize_code Impl.Blowfish.X86_64.decrypt

end VG
