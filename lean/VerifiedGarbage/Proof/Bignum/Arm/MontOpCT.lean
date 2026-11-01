module
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineBase
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineOpCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Impl.Bignum.Arm.MontOp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! # Fixed-index Montgomery operations have public traces -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand numAt arrAt)

theorem montOp_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (montOp o a b) (fun _ _ => True) :=
  montPipelineOp_ct montRound (MontPipeline.RoundLaw.loop MontPipeline.baseline_law)
    (MontPipeline.RoundCTLaw.loop MontPipeline.baseline_law MontPipeline.baseline_ct) ho ha hb fit

end VG.Proof.Bignum.Arm
