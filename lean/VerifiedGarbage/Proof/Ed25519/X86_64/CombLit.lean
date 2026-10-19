module

public import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
public import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
meta import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
import VerifiedGarbage.Impl.Ed25519.X86_64.FieldCheck
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ed25519.X86_64.FieldCheck
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-! Checked literals for the comb variant (its doublings' calls inlined, as its constant-time proof
reads it) and the registered code. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
materialize_code combMultiplyLit :=
  (combMultiply Impl.X25519.X86_64.baseline combSelect (Point64.bodies Impl.X25519.X86_64.baseline))
materialize_code combMultiplyAdxLit :=
  (combMultiply Impl.X25519.X86_64.adx combSelect (Point64.bodies Impl.X25519.X86_64.adx))
materialize_code combMultiplyAdxYLit :=
  (combMultiply Impl.X25519.X86_64.adx combSelectY (Point64.bodies Impl.X25519.X86_64.adx))
end VG.Proof.Ed25519.X86_64

namespace VG
materialize_code scalarBase_precomputedLit := (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline)
materialize_code scalarBase_precomputedAdxLit := (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.adx)
materialize_code scalarBase_adxLit := Impl.Ed25519.X86_64.scalarBase_adx
end VG
