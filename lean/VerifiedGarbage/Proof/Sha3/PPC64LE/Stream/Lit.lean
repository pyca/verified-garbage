module

public import VerifiedGarbage.Proof.Sha3.PPC64LE.Lit
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Lit
meta import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-!
# The SHA-3 sponge on PPC64LE: the code as literals

`absorb`, `pad` and `squeeze` as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), whose calls refer to the literal of the
permutation (`Proof/Sha3/PPC64LE/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream

materialize_code absorb := Impl.Sha3.PPC64LE.Stream.absorb
materialize_code pad := Impl.Sha3.PPC64LE.Stream.pad
materialize_code squeeze := Impl.Sha3.PPC64LE.Stream.squeeze

end VG.Proof.Sha3.PPC64LE.Stream
