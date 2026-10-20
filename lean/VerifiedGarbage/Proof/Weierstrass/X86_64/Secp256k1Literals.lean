module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64
public import VerifiedGarbage.Impl.Ecdh.X86_64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64
meta import VerifiedGarbage.Impl.Ecdh.X86_64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over secp256k1 on x86-64. Each generator is checked once here;
callers reuse its kernel-checked equality. The field operations modulo `p`
and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Secp256k1Literals
open VG VG.Impl.Ecdsa.X86_64 VG.Impl.Mont.X86_64

materialize_template mulPT := mulG secp256k1.MP'
materialize_template addPT := addR secp256k1.MP'
materialize_template subPT := subR secp256k1.MP'
materialize_template mulNT := mulG secp256k1.MN'
materialize_template addNT := addR secp256k1.MN'
materialize_template subNT := subR secp256k1.MN'

materialize_code pPow := Cfg.pPow secp256k1
materialize_code nPow := Cfg.nPow secp256k1
materialize_code gMulK := Cfg.gMulK secp256k1
materialize_code validate := Impl.Ecdh.X86_64.Cfg.validate secp256k1
materialize_code checkFn := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody secp256k1)
materialize_code check := Impl.Ecdh.X86_64.Cfg.check secp256k1

end VG.Proof.Weierstrass.X86_64.Secp256k1Literals
