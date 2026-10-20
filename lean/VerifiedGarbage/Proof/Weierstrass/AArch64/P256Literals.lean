module
public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdh.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit


/-! Shared literals for code used by signing, public-key derivation and ECDH.
Each generator is checked once here; callers reuse its kernel-checked equality. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.P256Literals
open VG VG.Impl.Ecdsa.AArch64

materialize_code pPow := Cfg.pPow p256
materialize_code nPow := Cfg.nPow p256
materialize_code checkBody := Impl.Ecdh.AArch64.Cfg.checkBody p256
materialize_code checkFn := Impl.Ecdh.AArch64.Cfg.checkFn p256
materialize_code validate := Impl.Ecdh.AArch64.Cfg.validate p256
materialize_code comb := Impl.Weierstrass.AArch64.TCombCfg.comb p256.combCfg

end VG.Proof.Weierstrass.AArch64.P256Literals
