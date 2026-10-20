module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
public import VerifiedGarbage.Impl.Ecdh.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
meta import VerifiedGarbage.Impl.Ecdh.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over secp256k1 on AArch64. Each generator is checked once
here; callers reuse its kernel-checked equality. The field operations modulo
`p` and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Secp256k1Literals
open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Mont.AArch64

materialize_template mulPT := mul secp256k1.MP'
materialize_template addPT := add secp256k1.MP'
materialize_template subPT := sub secp256k1.MP'
materialize_template mulNT := mul secp256k1.MN'
materialize_template addNT := add secp256k1.MN'
materialize_template subNT := sub secp256k1.MN'

materialize_template mulPIT := mul { secp256k1.MP' with tmp := secp256k1.invTmp }
materialize_template mulNIT := mul { secp256k1.MN' with tmp := secp256k1.invTmp }

materialize_code invFnP := Cfg.invFn secp256k1 (Cfg.pPowI secp256k1)
materialize_code invFnN := Cfg.invFn secp256k1 (Cfg.nPowI secp256k1)
materialize_code pPow := Cfg.pPow secp256k1
materialize_code nPow := Cfg.nPow secp256k1
materialize_code mulFn := Cfg.mulFn secp256k1
materialize_code checkBody := Impl.Ecdh.AArch64.Cfg.checkBody secp256k1
materialize_code checkFn := Impl.Ecdh.AArch64.Cfg.checkFn secp256k1
materialize_code validate := Impl.Ecdh.AArch64.Cfg.validate secp256k1

end VG.Proof.Weierstrass.AArch64.Secp256k1Literals
