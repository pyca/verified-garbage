import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
import VerifiedGarbage.Impl.Ecdh.Secp256k1.AArch64

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over secp256k1 on AArch64. Each generator is checked once
here; callers reuse its kernel-checked equality. The field operations modulo
`p` and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

namespace VG.Proof.Weierstrass.AArch64.Secp256k1Literals
open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Mont.AArch64

materialize_template mulPT := mul secp256k1.MP'
materialize_template addPT := add secp256k1.MP'
materialize_template subPT := sub secp256k1.MP'
materialize_template mulNT := mul secp256k1.MN'
materialize_template addNT := add secp256k1.MN'
materialize_template subNT := sub secp256k1.MN'

materialize_code pPow := Cfg.pPow secp256k1
materialize_code nPow := Cfg.nPow secp256k1
materialize_code validate := Impl.Ecdh.AArch64.Cfg.validate secp256k1

end VG.Proof.Weierstrass.AArch64.Secp256k1Literals
