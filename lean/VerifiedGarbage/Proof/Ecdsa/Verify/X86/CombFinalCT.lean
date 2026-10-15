module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
public import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCallTaint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCallTaint
import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.X25519.X86.Column
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# ECDSA verification over P-256 on x86 (32-bit): the final check's constant time

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

def vFinalCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.tail p256Comb
materialize_code vFinalCode

/-- The multiplication modulo `p`, whose analysis the summary below does once,
in place of each call. -/
def combMulPCode : Prog isa :=
  Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p256p.k Spec.Weierstrass.Mont.p256p.m
materialize_code combMulPCode
taint_summary combMulPSum : taint τComb combMulPCode

theorem vFinal_rel : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 4 false)) vFinalCode (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (scratchArgτ 4 false) vFinalCode h).isSome = true := by
    native_taint_decide_sum [combMulPSum]
  exact RelCT.taint (A := taint) _ (fun _ _ h => h) hc

end VG.Proof.Ecdsa.Verify.X86
