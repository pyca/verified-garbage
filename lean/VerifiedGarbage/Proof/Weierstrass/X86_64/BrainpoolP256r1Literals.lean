module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86_64
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.X86_64
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.X86_64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over brainpoolP256r1 on x86-64. Each generator is checked once here;
callers reuse its kernel-checked equality. The field operations modulo `p`
and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.BrainpoolP256r1Literals
open VG VG.Impl.Ecdsa.X86_64 VG.Impl.Mont.X86_64

materialize_template mulPT := mulG brainpoolp256r1.MP'
materialize_template addPT := addR brainpoolp256r1.MP'
materialize_template subPT := subR brainpoolp256r1.MP'
materialize_template mulNT := mulG brainpoolp256r1.MN'
materialize_template addNT := addR brainpoolp256r1.MN'
materialize_template subNT := subR brainpoolp256r1.MN'

materialize_code pPow := Cfg.pPow brainpoolp256r1
materialize_code nPow := Cfg.nPow brainpoolp256r1
materialize_code gMulK := Cfg.gMulK brainpoolp256r1
materialize_code validate := Impl.Ecdh.X86_64.Cfg.validate brainpoolp256r1
materialize_code checkFn := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody brainpoolp256r1)
materialize_code check := Impl.Ecdh.X86_64.Cfg.check brainpoolp256r1

end VG.Proof.Weierstrass.X86_64.BrainpoolP256r1Literals
