import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.P192.X86_64
import VerifiedGarbage.Impl.Ecdh.P192.X86_64

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over P-192 on x86-64. Each generator is checked once here;
callers reuse its kernel-checked equality. The field operations modulo `p`
and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

namespace VG.Proof.Weierstrass.X86_64.P192Literals
open VG VG.Impl.Ecdsa.X86_64 VG.Impl.Mont.X86_64

materialize_template mulPT := mulG p192.MP'
materialize_template addPT := addR p192.MP'
materialize_template subPT := subR p192.MP'
materialize_template mulNT := mulG p192.MN'
materialize_template addNT := addR p192.MN'
materialize_template subNT := subR p192.MN'

materialize_code pPow := Cfg.pPow p192
materialize_code nPow := Cfg.nPow p192
materialize_code gMulK := Cfg.gMulK p192
materialize_code validate := Impl.Ecdh.X86_64.Cfg.validate p192

end VG.Proof.Weierstrass.X86_64.P192Literals
