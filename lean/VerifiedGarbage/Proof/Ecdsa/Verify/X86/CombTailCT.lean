module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.X86.TComb
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
meta import VerifiedGarbage.Impl.Ecdsa.Verify.X86
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
# ECDSA verification over P-256 on x86 (32-bit): the tail's constant time

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

def vBitsCode : Prog isa := Impl.Weierstrass.X86.bits (p256Comb.sl U) (bitsAt p256Comb.n 0) (8 * p256Comb.n)
materialize_code vBitsCode

theorem vBits_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp, .edi] 4)) vBitsCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
def vSaveCode : Prog isa := .block (Impl.Ecdsa.Verify.X86.Cfg.save p256Comb)
def vSumCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.sum p256Comb
materialize_code vSaveCode
materialize_code vSumCode

theorem vSave_rel : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 4 false)) vSaveCode
    (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
theorem vSum_rel : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 4 false)) vSumCode
    (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
end VG.Proof.Ecdsa.Verify.X86
