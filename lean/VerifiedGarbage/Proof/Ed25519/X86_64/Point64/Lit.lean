module

import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
public import VerifiedGarbage.Impl.X25519.X86_64.Adx
meta import VerifiedGarbage.Impl.X25519.X86_64.Adx
public import VerifiedGarbage.Impl.Ed25519.X86_64.Point64
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Ed25519.X86_64.Point64
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-! The point functions' code as literals (`materialize_code`), which their checks, and those
of the code that calls them, read rather than build each field multiplication again. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86_64.Point64

open VG.Impl.X25519.X86_64 (baseline adx)

materialize_code doubleExtLit := doubleFn baseline true
materialize_code doubleProjLit := doubleFn baseline false
materialize_code addExtLit := addFn baseline true
materialize_code addProjLit := addFn baseline false
materialize_code doubleExtAdxLit := doubleFn adx true
materialize_code doubleProjAdxLit := doubleFn adx false
materialize_code addExtAdxLit := addFn adx true
materialize_code addProjAdxLit := addFn adx false
materialize_code addAffineLit := addAffineFn baseline
materialize_code addAffineAdxLit := addAffineFn adx

end VG.Impl.Ed25519.X86_64.Point64
