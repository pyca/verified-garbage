module

public import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# brainpoolP512r1 public keys on PPC64LE: the code as a literal

`vg_ec_brainpoolp512r1_public_key` as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`), which its constant time and `spSafe` evaluate.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.PPC64LE.publicKeyBrainpoolP512r1

end VG
