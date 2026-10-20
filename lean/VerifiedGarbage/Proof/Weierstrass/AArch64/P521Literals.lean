module

public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
public import VerifiedGarbage.Impl.Ecdh.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
meta import VerifiedGarbage.Impl.Ecdh.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over P-521 on AArch64. Each generator is checked once
here; callers reuse its kernel-checked equality. The field operations modulo
`p` and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.P521Literals
open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Mont.AArch64

materialize_template mulPT := mul p521.MP'
materialize_template addPT := add p521.MP'
materialize_template subPT := sub p521.MP'
materialize_template mulNT := mul p521.MN'
materialize_template addNT := add p521.MN'
materialize_template subNT := sub p521.MN'

materialize_template mulPIT := mul { p521.MP' with tmp := p521.invTmp }
materialize_template mulNIT := mul { p521.MN' with tmp := p521.invTmp }

materialize_code invFnP := Cfg.invFn p521 (Cfg.pPowI p521)
materialize_code invFnN := Cfg.invFn p521 (Cfg.nPowI p521)
materialize_code pPow := Cfg.pPow p521
materialize_code nPow := Cfg.nPow p521
materialize_code checkBody := Impl.Ecdh.AArch64.Cfg.checkBody p521
materialize_code checkFn := Impl.Ecdh.AArch64.Cfg.checkFn p521
materialize_code validate := Impl.Ecdh.AArch64.Cfg.validate p521
materialize_code comb := Impl.Weierstrass.AArch64.TCombCfg.comb p521.combCfg

end VG.Proof.Weierstrass.AArch64.P521Literals
