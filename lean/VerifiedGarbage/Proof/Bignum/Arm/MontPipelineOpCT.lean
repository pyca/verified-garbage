module
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTFnBody
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipelineOp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Impl.Bignum.Arm.MontPipelineOp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! # Fixed-index Montgomery operations have public traces -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand numAt arrAt)

theorem montPipelineOp_ct (round : Prog isa) (law : MontPipeline.LoopLaw round) (ctLaw : MontPipeline.LoopCTLaw round) {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (MontPipeline.op round o a b) (fun _ _ => True) := by
  let P := fun (s t : State) =>
    (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
    (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp
  have args : RelCT isa P (.block (montOpArgs o a b)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have ready := (relCT_keep_sp args (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨montOpArgs_ready s h.1.1 ho ha hb h.1.2, montOpArgs_ready t h.2.1.1 ho ha hb h.2.1.2⟩)
  have body := relCT_keep_sp ((MontPipeline.fnBody_ct round law ctLaw ho ha hb fit).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t)
    (fun _ _ h => h.2) (fun _ _ h => h)) (fun _ _ h => h.1)
  exact (ready.seq (body.seq (loadStack_ct .r0 0))).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
