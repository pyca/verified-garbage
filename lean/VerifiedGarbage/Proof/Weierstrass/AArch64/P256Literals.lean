import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64

/-! Shared literals for code used by signing, public-key derivation and ECDH.
Each generator is checked once here; callers reuse its kernel-checked equality. -/

namespace VG.Proof.Weierstrass.AArch64.P256Literals
open VG VG.Impl.Ecdsa.AArch64

materialize_code pPow := Cfg.pPow p256
materialize_code nPow := Cfg.nPow p256
materialize_code validate := Impl.Ecdh.AArch64.Cfg.validate p256
materialize_code comb := Impl.Weierstrass.AArch64.TCombCfg.comb p256.combCfg

end VG.Proof.Weierstrass.AArch64.P256Literals
