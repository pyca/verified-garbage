import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombTiming
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Proof.Framework.AArch64.Lit

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64

macro "jac_field_ct" : tactic => `(tactic|
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide))

theorem jacComb_checks : JacCombChecks p256.combCfg where
  init := by jac_field_ct
  digit := VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x19])
    (fun _ _ _ _ h => h) (by taint_decide)
  address := VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x19])
    (fun _ _ _ _ h => h) (by taint_decide)
  entry := VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x19,.x16])
    (fun _ _ _ _ h => h) (by taint_decide)
  mixed := {
    zero := by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl <;> jac_field_ct
    copyQ := by jac_field_ct
    init := by jac_field_ct
    head := by jac_field_ct
    tail := by jac_field_ct
    double := Forward.rd_ct
    infinity := by jac_field_ct }
  copy := by jac_field_ct

theorem jacComb_finish_ct : FieldCT (Jacobian.jacCombFinish p256.combCfg) := by jac_field_ct

macro "jac_reg_ct" rs:term : tactic => `(tactic|
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs $rs)
    (fun _ _ _ _ h => h) (by taint_decide))

theorem jacTree_copy_preserves : ∀ r∈[Reg.x19,Reg.x20],
    ∀ i∈instrs (.block (VG.Impl.Weierstrass.AArch64.copyPt (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).M.n
      (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).R (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).D) : Prog isa),dstOf i≠some r := by
  decide

theorem jacWindow_infinity_ct : FieldCT (.block (Jacobian.infinity
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256)
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).R)) := by jac_field_ct

theorem jacWindow_finish_ct : FieldCT (Jacobian.jacFinish
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256)) := by jac_field_ct

theorem jacSumTail_ct : FieldCT (.seq
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.sum p256)
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.tail p256)) := by jac_field_ct

theorem jacSave_ct : FieldCT (.block (VG.Impl.Ecdsa.Verify.AArch64.Cfg.save p256)) := by jac_field_ct

theorem jacPrefix_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (verifyPrefix p256) := by
  jac_reg_ct [.x0,.x1,.x2,.x3]

end VG.Proof.Ecdsa.Verify.AArch64
