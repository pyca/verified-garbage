import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdh.P521.X86_64

/-! Shared literals for code used by signing, public-key derivation and ECDH.
Each generator is checked once here; callers reuse its kernel-checked equality. -/

namespace VG.Proof.Weierstrass.X86_64.P521Literals
open VG VG.Impl.Ecdsa.X86_64

materialize_code pPow := Cfg.pPow p521
materialize_code nPow := Cfg.nPow p521
materialize_code gMulK := Cfg.gMulK p521
materialize_code validate := Impl.Ecdh.X86_64.Cfg.validate p521
materialize_code pPowAdx := Cfg.pPow p521x
materialize_code nPowAdx := Cfg.nPow p521x
materialize_code gMulKAdx := Cfg.gMulK p521x
materialize_code validateAdx := Impl.Ecdh.X86_64.Cfg.validate p521x

end VG.Proof.Weierstrass.X86_64.P521Literals
