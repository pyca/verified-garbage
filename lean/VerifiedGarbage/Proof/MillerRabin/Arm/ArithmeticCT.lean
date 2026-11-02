module
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRounds
public import VerifiedGarbage.Impl.MillerRabin.Arm.Arithmetic
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTFnBody
import VerifiedGarbage.Proof.Bignum.Arm.FiosFastRound
import VerifiedGarbage.Proof.Bignum.Arm.FiosFastCT
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Impl.Bignum.Arm.MontOp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! # Fixed-index Montgomery operations have public traces -/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm.Arithmetic
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Impl.MillerRabin.Arm.Arithmetic
open VG.Proof.Rsa.Mont (Operand numAt arrAt)

private theorem product_fios_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (product true o a b) (fun _ _ => True) := by
  let P := fun (s t : State) =>
    (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
    (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp
  have args : RelCT isa P (.block (montOpArgs o a b)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have ready := (relCT_keep_sp args (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨montOpArgs_ready s h.1.1 ho ha hb h.1.2, montOpArgs_ready t h.2.1.1 ho ha hb h.2.1.2⟩)
  have body := relCT_keep_sp ((MontPipeline.fnBody_ct FiosFast.round (MontPipeline.RoundLaw.loop FiosFast.round_law)
    (MontPipeline.RoundCTLaw.loop FiosFast.round_law (by intro _ _ _ _ _ _ _ _ _ _ hi; exact FiosFast.round_ct hi)) ho ha hb fit).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t)
    (fun _ _ h => h.2) (fun _ _ h => h)) (fun _ _ h => h.1)
  simp only [product, ↓reduceIte]
  exact (ready.seq (body.seq (loadStack_ct .r0 0))).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem product_ct (fios : Bool) {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (product fios o a b) (fun _ _ => True) := by
  cases fios with
  | false => exact montOp_ct ho ha hb fit
  | true => exact product_fios_ct ho ha hb fit

theorem square_ct (fios : Bool) {base : BitVec 32} {len w o a : Nat}
    (ho : Operand o) (ha : Operand a) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w a < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (square fios o a) (fun _ _ => True) := by
  cases fios with
  | false => exact squareOp_ct ho ha
  | true => exact product_fios_ct ho ha ha fit

end VG.Proof.MillerRabin.Arm.Arithmetic
