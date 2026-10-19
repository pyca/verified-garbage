module

public import VerifiedGarbage.Impl.X25519.X86_64.Base
meta import VerifiedGarbage.Impl.X25519.X86_64.Base
public import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
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

/-! Checked literals for the comb with AVX512_IFMA, and the functions running it. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Zmm
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
materialize_code combMultiplyLit := (Impl.Ed25519.X86_64.Zmm.combMultiply Impl.X25519.X86_64.adx)
end VG.Proof.Ed25519.X86_64.Zmm

namespace VG
materialize_code scalarBase_ifmaLit := Impl.Ed25519.X86_64.scalarBase_ifma
materialize_code x25519BaseIfmaLit := Impl.X25519.X86_64.Base.x25519BaseIfma
end VG
