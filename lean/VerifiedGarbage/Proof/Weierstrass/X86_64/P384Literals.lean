import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdh.P384.X86_64

/-! Shared literals for code used by signing, public-key derivation and ECDH.
Each generator is checked once here; callers reuse its kernel-checked equality. -/

namespace VG.Proof.Weierstrass.X86_64.P384Literals
open VG VG.Impl.Ecdsa.X86_64

materialize_code pPow := Cfg.pPow p384
materialize_code nPow := Cfg.nPow p384
materialize_code gMulK := Cfg.gMulK p384
materialize_code validate := Impl.Ecdh.X86_64.Cfg.validate p384
materialize_code pPowAdx := Cfg.pPow p384x
materialize_code nPowAdx := Cfg.nPow p384x
materialize_code gMulKAdx := Cfg.gMulK p384x
materialize_code validateAdx := Impl.Ecdh.X86_64.Cfg.validate p384x

end VG.Proof.Weierstrass.X86_64.P384Literals
