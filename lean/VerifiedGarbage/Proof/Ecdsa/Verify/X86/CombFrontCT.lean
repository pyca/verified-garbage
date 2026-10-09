import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT

/-!
# ECDSA verification over P-256 on x86 (32-bit): the front's constant time

One of the comb verifier's constant-time checks, each in a module of its own
(`CombFrontCT`, `CombMidCT`, `CombTailCT`, `CombFinalCT`), checked in
parallel; `CombStagesCT` composes them.
-/

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.Ecdsa.Verify.X86

def vFrontCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.combFront p256Comb
materialize_code vFrontCode

/-- The front starts at the function's entry: its arguments public, the
fourth the base of the working space, and the calls' stack below. -/
def vFrontτ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8192], argLen := 20, argBases := [(16, 0)],
    room := 20 }

theorem vFront_rel : RelCT isa (VG.X86.Taint.Agree vFrontτ) vFrontCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86
