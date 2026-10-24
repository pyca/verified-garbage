module

public import VerifiedGarbage.Impl.EcKey.Compressed.P192.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.P192.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEC 1 point conversion over P-192 on PPC64LE: the code as literals

`vg_ec_p192_compress_public_key` as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`), which its constant time and `spSafe` evaluate.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.Compressed.PPC64LE.compressP192

end VG
