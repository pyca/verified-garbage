module
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
import VerifiedGarbage.Impl.Ecdh.P384.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ecdh.P384.X86_64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target


/-! Shared literals for code used by signing, public-key derivation and ECDH.
Each generator is checked once here; callers reuse its kernel-checked equality.
The field operations modulo `p` are templates (`materialize_template`): every
product, square, sum and difference of the code reads its template rather than
being built again. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P384Literals
open VG VG.Impl.Ecdsa.X86_64 VG.Impl.Mont.X86_64

materialize_template mulT := mulG p384.MP'
materialize_template sqrT := sqrS p384.MP'
materialize_template addT := addR p384.MP'
materialize_template mulAdxT := mulG p384x.MP'
materialize_template sqrAdxT := sqrS p384x.MP'
materialize_template addAdxT := addR p384x.MP'
materialize_template subT := sub384

materialize_code pPow := Cfg.pPow p384
materialize_code nPow := Cfg.nPow p384
materialize_code gMulK := Cfg.gMulK p384
materialize_code validate := Impl.Ecdh.X86_64.Cfg.validate p384
materialize_code checkFn := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody p384)
materialize_code check := Impl.Ecdh.X86_64.Cfg.check p384
materialize_code pPowAdx := Cfg.pPow p384x
materialize_code nPowAdx := Cfg.nPow p384x
materialize_code gMulKAdx := Cfg.gMulK p384x
materialize_code validateAdx := Impl.Ecdh.X86_64.Cfg.validate p384x
materialize_code checkFnAdx := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody p384x)
materialize_code checkAdx := Impl.Ecdh.X86_64.Cfg.check p384x

end VG.Proof.Weierstrass.X86_64.P384Literals
