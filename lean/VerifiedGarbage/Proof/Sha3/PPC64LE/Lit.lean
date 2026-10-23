module

public import VerifiedGarbage.Impl.Sha3.PPC64LE
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha3.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-!
# Keccak-f[1600] on PPC64LE: the code as a literal

The permutation's code as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`): its prologue stores the round constants, which
the kernel would otherwise compute in every check that evaluates the code.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE

materialize_code permute := Impl.Sha3.PPC64LE.permute

end VG.Proof.Sha3.PPC64LE
