module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCT
public import VerifiedGarbage.Impl.Ecdsa.P256.X86Comb
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.X86.TComb
meta import VerifiedGarbage.Impl.Ecdsa.Verify.X86
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCT
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86Comb
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
meta import VerifiedGarbage.Proof.Weierstrass.WinLay
meta import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# ECDSA verification over P-256 on x86 (32-bit): the front's constant time

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

def vFrontCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.combFront p256Comb
materialize_code vFrontCode

theorem vFront_rel : RelCT isa (VG.X86.Taint.Agree vFrontτ) vFrontCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86
