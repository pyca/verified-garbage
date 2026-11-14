module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LEComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LEComb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# brainpoolP512r1 public keys by the comb on PPC64LE: the code as a literal

`vg_ec_brainpoolp512r1_public_key` with `[d]G` by the comb as a literal
(`materialize_code`, `Proof/Framework/Lit.lean`), which its constant time
evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.PPC64LE.publicKeyBrainpoolP512r1Comb

end VG
