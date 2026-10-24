module

public import VerifiedGarbage.Impl.EcKey.Compressed.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Secp256k1.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEC 1 point conversion over secp256k1 on PPC64LE: the code as literals

`vg_ec_secp256k1_compress_public_key` and `_decompress_public_key` as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which their constant time and `spSafe` evaluate.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.Compressed.PPC64LE.compressSecp256k1
materialize_code Impl.EcKey.Compressed.PPC64LE.decompressSecp256k1

end VG
