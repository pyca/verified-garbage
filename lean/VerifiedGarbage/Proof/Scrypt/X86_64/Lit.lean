module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Scrypt.X86_64.RoMixDirect
meta import VerifiedGarbage.Impl.Scrypt.X86_64.RoMixDirect
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# scrypt on X86_64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Scrypt.X86_64.salsa
materialize_code Impl.Scrypt.X86_64.blockMix
materialize_code Impl.Scrypt.X86_64.blockMixFused
materialize_code Impl.Scrypt.X86_64.roMix

materialize_code Impl.Scrypt.X86_64.roMixDirect

end VG
