module

public import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Ecdh.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
import VerifiedGarbage.Impl.Ecdh.P224.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ecdh.P224.X86_64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over P-224 on x86-64. Each generator is checked once here;
callers reuse its kernel-checked equality. The field operations modulo `p`
and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P224Literals
open VG VG.Impl.Ecdsa.X86_64 VG.Impl.Mont.X86_64

materialize_template mulPT := mulG p224.MP'
materialize_template addPT := addR p224.MP'
materialize_template subPT := subR p224.MP'
materialize_template mulNT := mulG p224.MN'
materialize_template addNT := addR p224.MN'
materialize_template subNT := subR p224.MN'

materialize_code pPow := Cfg.pPow p224
materialize_code nPow := Cfg.nPow p224
materialize_code gMulK := Cfg.gMulK p224
materialize_code validate := Impl.Ecdh.X86_64.Cfg.validate p224
materialize_code checkFn := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody p224)
materialize_code check := Impl.Ecdh.X86_64.Cfg.check p224

end VG.Proof.Weierstrass.X86_64.P224Literals
