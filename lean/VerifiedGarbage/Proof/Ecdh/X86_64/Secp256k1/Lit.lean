module

import VerifiedGarbage.Impl.Ecdh.Secp256k1.X86_64
meta import VerifiedGarbage.Impl.Ecdh.Secp256k1.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Secp256k1Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Secp256k1Literals
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.Secp256k1

open VG.Impl.Ecdh.X86_64

materialize_code exchangeSecp256k1

end VG.Proof.Ecdh.X86_64.Secp256k1
