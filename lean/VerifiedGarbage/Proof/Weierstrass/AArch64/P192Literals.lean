import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.P192.AArch64
import VerifiedGarbage.Impl.Ecdh.P192.AArch64

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over P-192 on AArch64. Each generator is checked once
here; callers reuse its kernel-checked equality. The field operations modulo
`p` and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

namespace VG.Proof.Weierstrass.AArch64.P192Literals
open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Mont.AArch64

materialize_template mulPT := mul p192.MP'
materialize_template addPT := add p192.MP'
materialize_template subPT := sub p192.MP'
materialize_template mulNT := mul p192.MN'
materialize_template addNT := add p192.MN'
materialize_template subNT := sub p192.MN'

materialize_code pPow := Cfg.pPow p192
materialize_code nPow := Cfg.nPow p192
materialize_code validate := Impl.Ecdh.AArch64.Cfg.validate p192

end VG.Proof.Weierstrass.AArch64.P192Literals
