module

public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.X86_64
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP256r1Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP256r1Literals
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.BrainpoolP256r1

open VG.Impl.Ecdh.X86_64

materialize_code exchangeBrainpoolP256r1

end VG.Proof.Ecdh.X86_64.BrainpoolP256r1
