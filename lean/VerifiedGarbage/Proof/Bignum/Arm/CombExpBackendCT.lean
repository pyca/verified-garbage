module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT

/-! Shared arithmetic timing does not require the secret exponent bytes to agree. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Spec.Rsa.Mont (Operand)

theorem arithmetic_ct (backend : MontBackend) (base source table sp : BitVec 32)
    (len w M g N : Nat) (bs : List Byte) (o a b : Nat)
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t=>
      TwoExp.OpInput base len w (TwoExp.CallReady base sp len) b s ∧
      TwoExp.OpInput base len w (TwoExp.CallReady base sp len) b t ∧ s.sp=t.sp)
      ((arithmetic backend base source table sp len w M g N bs).op o a b) (fun _ _=>True) := by
  have timing := TwoExp.sharedMontgomeryTiming base sp len w backend.name backend.mul
    (fun _ _ _ ho ha hb s h=>backend.correct s h ho ha hb) backend.stackOk
    (fun _ _ _ ho ha hb=>backend.rawCT ho ha hb)
  exact timing.op_ct o a b ho ha hb

end VG.Proof.Bignum.Arm.CombExp
