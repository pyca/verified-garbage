module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
public import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
public import VerifiedGarbage.Proof.Weierstrass.X86.NafPrepTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafPrepTiming
import VerifiedGarbage.Proof.Framework.X86.TaintSym
meta import VerifiedGarbage.Proof.Framework.X86.TaintSym
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.NativeTaint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.X25519.X86.Column
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.X25519.X86.Column

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86

def nafPrepInitCode : Prog isa := .block (Naf.init (p256Comb.sl V) 3520)
def nafPrepStepCode : Prog isa := Naf.step 3580 3520
materialize_code nafPrepInitCode
materialize_code nafPrepStepCode

theorem nafPrep_checks : NafPrepChecks 3580 (p256Comb.sl V) 3520 := by
  refine ⟨?_,?_⟩
  · change ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (nafτ [.edi])) nafPrepInitCode
    exact Taint.constantTime (A:=taint) _ (fun _ _ _ _ h => h) (by native_taint_decide)
  · change ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (nafPrepτ 3520)) nafPrepStepCode
    exact Taint.constantTime (A:=taint) _ (fun _ _ _ _ h => h) (by native_taint_decide)

end VG.Proof.Ecdsa.Verify.X86
