module

public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP256r1.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEC 1 point conversion over brainpoolP256r1 on PPC64LE: the code as literals

`vg_ec_brainpoolp256r1_compress_public_key` as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`), which its constant time and `spSafe` evaluate.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP256r1

end VG
