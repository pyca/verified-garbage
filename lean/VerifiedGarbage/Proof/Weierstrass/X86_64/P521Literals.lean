module
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
import VerifiedGarbage.Impl.Ecdh.P521.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ecdh.P521.X86_64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target


/-! Shared literals for code used by signing, public-key derivation and ECDH.
Each generator is checked once here; callers reuse its kernel-checked equality. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521Literals
open VG VG.Impl.Ecdsa.X86_64

materialize_code pPow := Cfg.pPow p521
materialize_code nPow := Cfg.nPow p521
materialize_code gMulK := Cfg.gMulK p521
materialize_code validate := Impl.Ecdh.X86_64.Cfg.validate p521
materialize_code checkFn := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody p521)
materialize_code check := Impl.Ecdh.X86_64.Cfg.check p521
materialize_code pPowAdx := Cfg.pPow p521x
materialize_code nPowAdx := Cfg.nPow p521x
materialize_code gMulKAdx := Cfg.gMulK p521x
materialize_code validateAdx := Impl.Ecdh.X86_64.Cfg.validate p521x
materialize_code checkFnAdx := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody p521x)
materialize_code checkAdx := Impl.Ecdh.X86_64.Cfg.check p521x

end VG.Proof.Weierstrass.X86_64.P521Literals
