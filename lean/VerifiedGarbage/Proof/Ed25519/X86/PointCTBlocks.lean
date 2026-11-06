module

public import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.X25519.X86.Field32.Pow250Sum
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
public import VerifiedGarbage.Impl.Ed25519.X86.PointEncode
public import VerifiedGarbage.Impl.Ed25519.X86.PointPowers
public import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Pow250Sum
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Impl.Ed25519.X86.PointEncode
meta import VerifiedGarbage.Impl.Ed25519.X86.PointPowers
meta import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# Constant time of the point arithmetic blocks

## The encoding

The point encoding's inversion calls `vg_gf25519_r32_pow250`, which the
analysis follows (`callTaint₀`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

/-! ## The checks -/

theorem pointEncode_ct {x : BitVec 32} : RelCT isa (CallCTPre x) pointEncode (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check callTaint₀ pointEncode h).isSome = true := by
    native_taint_decide_sum [VG.Proof.X25519.X86.pow250Sum]
  exact VG.RelCT.taint (A := taint) callTaint₀ (fun _ _ h => callTaint₀_agree h) hc

/-- What is public at the loop of doublings of `double16`. -/
def doubleTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esi, .edi], flags := false, lens := [0, 8192], bases := [(.edi, 1, 0)] }

/-! The body of the loop of doublings, which both `powersBody 1024 16` and
`powersBody 1024 32` run: analysed once, as a summary. -/

taint_summary doubleSum : taint doubleTaint (.block doubleBody)

end VG.Proof.Ed25519.X86
