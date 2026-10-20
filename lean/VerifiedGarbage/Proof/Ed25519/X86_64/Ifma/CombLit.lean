module

public import VerifiedGarbage.Impl.X25519.X86_64.Base
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
public import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
public import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.X25519.X86_64.Base
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.X25519.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

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
