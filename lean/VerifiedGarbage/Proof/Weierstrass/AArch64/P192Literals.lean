module

public import VerifiedGarbage.Impl.Ecdsa.P192.AArch64
public import VerifiedGarbage.Impl.Ecdh.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.P192.AArch64
meta import VerifiedGarbage.Impl.Ecdh.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over P-192 on AArch64. Each generator is checked once
here; callers reuse its kernel-checked equality. The field operations modulo
`p` and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.P192Literals
open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Mont.AArch64

materialize_template mulPT := mul p192.MP'
materialize_template addPT := add p192.MP'
materialize_template subPT := sub p192.MP'
materialize_template mulNT := mul p192.MN'
materialize_template addNT := add p192.MN'
materialize_template subNT := sub p192.MN'

materialize_template mulPIT := mul { p192.MP' with tmp := p192.invTmp }
materialize_template mulNIT := mul { p192.MN' with tmp := p192.invTmp }

materialize_code invFnP := Cfg.invFn p192 (Cfg.pPowI p192)
materialize_code invFnN := Cfg.invFn p192 (Cfg.nPowI p192)
materialize_code pPow := Cfg.pPow p192
materialize_code nPow := Cfg.nPow p192
materialize_code mulFn := Cfg.mulFn p192
materialize_code checkBody := Impl.Ecdh.AArch64.Cfg.checkBody p192
materialize_code checkFn := Impl.Ecdh.AArch64.Cfg.checkFn p192
materialize_code validate := Impl.Ecdh.AArch64.Cfg.validate p192

end VG.Proof.Weierstrass.AArch64.P192Literals
