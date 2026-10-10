import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
import VerifiedGarbage.Impl.Ecdh.P224.AArch64

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over P-224 on AArch64. Each generator is checked once
here; callers reuse its kernel-checked equality. The field operations modulo
`p` and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

namespace VG.Proof.Weierstrass.AArch64.P224Literals
open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Mont.AArch64

materialize_template mulPT := mul p224.MP'
materialize_template addPT := add p224.MP'
materialize_template subPT := sub p224.MP'
materialize_template mulNT := mul p224.MN'
materialize_template addNT := add p224.MN'
materialize_template subNT := sub p224.MN'

materialize_code pPow := Cfg.pPow p224
materialize_code nPow := Cfg.nPow p224
materialize_code validate := Impl.Ecdh.AArch64.Cfg.validate p224
materialize_code comb := Impl.Weierstrass.AArch64.TCombCfg.comb p224.combCfg

end VG.Proof.Weierstrass.AArch64.P224Literals
