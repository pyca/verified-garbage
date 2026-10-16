module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64
import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP384r1

open VG.Impl.Ecdsa.X86_64

materialize_code signBrainpoolP384r1

end VG.Proof.Ecdsa.X86_64.BrainpoolP384r1
