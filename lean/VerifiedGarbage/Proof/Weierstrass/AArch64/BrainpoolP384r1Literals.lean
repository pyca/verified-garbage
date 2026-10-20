module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64
public import VerifiedGarbage.Impl.Ecdh.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64
meta import VerifiedGarbage.Impl.Ecdh.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Shared literals for code used by signing, verification, public-key
derivation and ECDH over brainpoolP384r1 on AArch64. Each generator is checked once
here; callers reuse its kernel-checked equality. The field operations modulo
`p` and `n` are templates (`materialize_template`): every product, sum and
difference of the code reads its template rather than being built again. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Mont.AArch64

materialize_template mulPT := mul brainpoolp384r1.MP'
materialize_template addPT := add brainpoolp384r1.MP'
materialize_template subPT := sub brainpoolp384r1.MP'
materialize_template mulNT := mul brainpoolp384r1.MN'
materialize_template addNT := add brainpoolp384r1.MN'
materialize_template subNT := sub brainpoolp384r1.MN'

materialize_template mulPIT := mul { brainpoolp384r1.MP' with tmp := brainpoolp384r1.invTmp }
materialize_template mulNIT := mul { brainpoolp384r1.MN' with tmp := brainpoolp384r1.invTmp }

materialize_code invFnP := Cfg.invFn brainpoolp384r1 (Cfg.pPowI brainpoolp384r1)
materialize_code invFnN := Cfg.invFn brainpoolp384r1 (Cfg.nPowI brainpoolp384r1)
materialize_code pPow := Cfg.pPow brainpoolp384r1
materialize_code nPow := Cfg.nPow brainpoolp384r1
materialize_code mulFn := Cfg.mulFn brainpoolp384r1
materialize_code checkBody := Impl.Ecdh.AArch64.Cfg.checkBody brainpoolp384r1
materialize_code checkFn := Impl.Ecdh.AArch64.Cfg.checkFn brainpoolp384r1
materialize_code validate := Impl.Ecdh.AArch64.Cfg.validate brainpoolp384r1

end VG.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
