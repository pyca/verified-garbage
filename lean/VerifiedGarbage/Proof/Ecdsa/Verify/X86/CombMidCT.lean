module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCallTaint
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.X86.TComb
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCallTaint
meta import VerifiedGarbage.Impl.Ecdsa.Verify.X86
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.WinLay
meta import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ECDSA verification over P-256 on x86 (32-bit): the middle's constant time

One of the comb verifier's constant-time checks, each in a module of its own
(`CombFrontCT`, `CombMidCT`, `CombTailCT`, `CombFinalCT`), checked in
parallel; `CombStagesCT` composes them.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.Ecdsa.Verify.X86

def vMidCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.combMid p256Comb
materialize_code vMidCode

/-- The multiplication modulo `n`, whose analysis the summary below does once,
in place of each call. -/
def combMulNCode : Prog isa :=
  Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p256n.k Impl.Weierstrass.Mont.p256n.m
materialize_code combMulNCode
taint_summary combMulNSum : taint τComb combMulNCode

theorem vMid_rel : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 4 false)) vMidCode (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (scratchArgτ 4 false) vMidCode h).isSome = true := by
    native_taint_decide_sum [combMulNSum]
  exact RelCT.taint (A := taint) _ (fun _ _ h => h) hc

end VG.Proof.Ecdsa.Verify.X86
