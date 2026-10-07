import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCache

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64.P256Joint
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

theorem jointPrefix_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (jointPrefix p256) := by
  jac_reg_ct [.x0,.x1,.x2,.x3]

theorem jointTail_ct : FieldCT (Impl.Ecdsa.Verify.AArch64.Cfg.tail p256) := by
  jac_field_ct

theorem jointCache_ct : FieldCT (CachedJac.cache cfg.K) := by
  jac_field_ct

theorem jointFinish_ct : FieldCT (Jacobian.jacFinish cfg.K) := by
  jac_field_ct

theorem jointInit_ct : FieldCT (.block (Jacobian.infinity cfg.K cfg.K.R ++ ([.movz .x .x19 256 0] : List Instr))) := by
  jac_field_ct

end VG.Proof.Ecdsa.Verify.AArch64
