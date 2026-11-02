module

import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRounds
public import VerifiedGarbage.Impl.Bignum.Arm.MontCallFios
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineFnBody
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithFn
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithContract
public import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmeticCaller
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
public import VerifiedGarbage.Proof.Framework.RelCT

/-! A fused scanning round supplies the existing shared callable Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem montCallFios_law
    (law : MontPipeline.RoundLaw FiosFast.round)
    (ctLaw : MontPipeline.RoundCTLaw FiosFast.round) :
    CallArithmeticLaw MontCallFios.arithmetic where
  correct := by
    intro s base len w o a b h ho ha hb
    have body := MontPipeline.fnBody_ok FiosFast.round (MontPipeline.RoundLaw.loop law) s h.input.workspace h.input.layout
      ho ha hb h.input.ptr h.input.outIndex h.input.aIndex h.input.bIndex
      (by rw [h.input.width]; exact h.input.inverse)
      (by rw [h.input.width]; exact h.input.operand)
    simpa only [MontCallFios.arithmetic,h.input.width] using body
  ct := by
    intro base len w o a b ho ha hb fit s t tr1 tr2 u v h e1 e2
    exact MontPipeline.fnBody_ct FiosFast.round (MontPipeline.RoundLaw.loop law) (MontPipeline.RoundCTLaw.loop law ctLaw) ho ha hb fit
      s t tr1 tr2 u v ⟨h.1.input,h.2.1.input⟩ e1 e2
  stack := rfl

def montCallFios_backend
    (law : MontPipeline.RoundLaw FiosFast.round)
    (ctLaw : MontPipeline.RoundCTLaw FiosFast.round) : MontBackend where
  mul := MontCallFios.code
  verified := montCallWith_verified _ (montCallFios_law law ctLaw)
  correct := montCallWithFn_ok _ (montCallFios_law law ctLaw)
  rawCT := montCallWithFn_ct _ (montCallFios_law law ctLaw)
  stackOk := montCallWith_stack _ (montCallFios_law law ctLaw)
  caller := umaalArithmeticCaller
  suffix := "_umaal"
  features := ["umaal"]

end VG.Proof.Bignum.Arm
