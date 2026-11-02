module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallFios2
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineFnBody
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithFn
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithContract
public import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmeticCaller
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Framework.RelCT

/-! The two-row round supplies the shared callable Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem montCallFios2_law
    (law : MontPipeline.LoopLaw Fios2.round)
    (ctLaw : MontPipeline.LoopCTLaw Fios2.round) :
    CallArithmeticLaw MontCallFios2.arithmetic where
  correct := by
    intro s base len w o a b h ho ha hb
    have body := MontPipeline.fnBody_ok Fios2.round law s h.input.workspace h.input.layout
      ho ha hb h.input.ptr h.input.outIndex h.input.aIndex h.input.bIndex
      (by rw [h.input.width]; exact h.input.inverse)
      (by rw [h.input.width]; exact h.input.operand)
    simpa only [MontCallFios2.arithmetic, h.input.width] using body
  ct := by
    intro base len w o a b ho ha hb fit s t tr1 tr2 u v h e1 e2
    exact MontPipeline.fnBody_ct Fios2.round law ctLaw ho ha hb fit
      s t tr1 tr2 u v ⟨h.1.input, h.2.1.input⟩ e1 e2
  stack := rfl

def montCallFios2_backend
    (law : MontPipeline.LoopLaw Fios2.round)
    (ctLaw : MontPipeline.LoopCTLaw Fios2.round) : MontBackend where
  mul := MontCallFios2.code
  verified := montCallWith_verified _ (montCallFios2_law law ctLaw)
  correct := montCallWithFn_ok _ (montCallFios2_law law ctLaw)
  rawCT := montCallWithFn_ct _ (montCallFios2_law law ctLaw)
  stackOk := montCallWith_stack _ (montCallFios2_law law ctLaw)
  caller := umaalArithmeticCaller
  suffix := "_umaal"
  features := ["umaal"]

end VG.Proof.Bignum.Arm
