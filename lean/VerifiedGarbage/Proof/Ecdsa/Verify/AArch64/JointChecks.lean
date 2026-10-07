import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.CachedChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

theorem jointMixed_checks : JointMixedChecks P256Joint.cfg.K P256Joint.cfg.K.R
    P256Joint.cfg.K.E P256Joint.cfg.K.D where
  zero := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> jac_field_ct
  copyQ := by jac_field_ct
  init := by jac_field_ct
  head := Forward.ArithmeticMixedHead.ct
  tail := Forward.ArithmeticMixedTail.ct
  double := Forward.rd_ct
  infinity := by jac_field_ct

theorem jointFixed_checks : JointFixedChecks P256Joint.cfg where
  lookup := VG.Taint.constantTime (A:=taintS [P256Joint.cfg.tsym]) (Taint.ofRegs [.x0,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)
  sign := by jac_reg_ct [.x0,.x19]
  neg := by jac_field_ct
  read := by jac_reg_ct [.x0,.x19]
  mixed := jointMixed_checks
  copy := by jac_field_ct

theorem jointGPrep_checks : FastPrepChecks P256Joint.cfg.G (p256.sl U) 7 where
  init := by jac_reg_ct [.x0]
  step := by jac_reg_ct [.x0,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x20]

theorem jointQPrep_checks : FastPrepChecks P256Joint.cfg.K (p256.sl V) 5 where
  init := by jac_reg_ct [.x0]
  step := by jac_reg_ct [.x0,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x20]

theorem cachedDigit_checks : CachedField.DigitChecks where
  entry := { lookup := by jac_reg_ct [.x0,.x2]
             sign := by jac_reg_ct [.x0,.x19]
             neg := by jac_field_ct }
  add := cachedAdd_checks
  copy := by jac_field_ct
  digit := by jac_reg_ct [.x0,.x19]

end VG.Proof.Ecdsa.Verify.AArch64
