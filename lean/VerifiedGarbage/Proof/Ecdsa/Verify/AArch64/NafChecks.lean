import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindowTiming

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

theorem nafStep_checks : NafStepChecks (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256) where
  double := Forward.rd_ct
  copy := by jac_field_ct
  digit := {
    entry := {
      lookup := by jac_reg_ct [.x0,.x2]
      sign := by jac_reg_ct [.x0,.x19]
      neg := by jac_field_ct }
    add := {
      zero := by
        intro a ha
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> jac_field_ct
      copyP := by jac_field_ct
      copyQ := by jac_field_ct
      head := by jac_field_ct
      tail := by jac_field_ct
      double := Forward.rd_ct
      infinity := by jac_field_ct }
    copy := by jac_field_ct
    digit := by jac_reg_ct [.x0,.x19] }
  dec := by jac_reg_ct [.x19]


/-- The register-forwarded doubling of the table additions is
`Forward.P256RD`'s literal, so the kernel never runs the optimizer here. -/
theorem jacWinCfg_double_lit : VG.Impl.P256.VerifyDouble.double
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).M (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).S
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).R (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).D =
    .block Forward.P256Bounds.rightRD.lit := by
  change VG.Impl.P256.VerifyDouble.double VG.Impl.P256.VerifyDouble.M VG.Impl.P256.VerifyDouble.S
    VG.Impl.P256.VerifyDouble.R VG.Impl.P256.VerifyDouble.D = _
  rw [VG.Impl.P256.VerifyDouble.double,ite_eq_left
    (show VG.Impl.P256.VerifyDouble.selected VG.Impl.P256.VerifyDouble.M VG.Impl.P256.VerifyDouble.S
      VG.Impl.P256.VerifyDouble.R VG.Impl.P256.VerifyDouble.D from ⟨rfl,rfl,Or.inl ⟨rfl,rfl⟩⟩)]
  exact congrArg Code.block Forward.P256RD.optimized_lit

private abbrev Kc := VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256

private theorem nafTable_add_preserves : ∀ r∈[Reg.x19,Reg.x20],
    ∀ i∈instrs (Jacobian.jacAdd Kc Kc.R (Naf.twice Kc) Kc.D),dstOf i≠some r := by
  rw [Jacobian.jacAdd,jacWinCfg_double_lit]
  have h : (instrs (.seq (.block (zeroMask Kc.M.n Kc.R.z)) <|
      .ite (.nonzero .x .x2) (.block (copyPt Kc.M.n Kc.D (Naf.twice Kc))) <|
      .seq (.block (zeroMask Kc.M.n (Naf.twice Kc).z)) <|
      .ite (.nonzero .x .x2) (.block (copyPt Kc.M.n Kc.D Kc.R)) <|
      .seq (fprogB Kc.M (VG.Impl.Weierstrass.jacHead Kc.S Kc.R (Naf.twice Kc))) <|
      .seq (.block (zeroMask Kc.M.n Kc.S.t3)) <|
      .ite (.nonzero .x .x2)
        (.seq (.block (zeroMask Kc.M.n Kc.S.t5)) <|
          .ite (.nonzero .x .x2) (.block Forward.P256Bounds.rightRD.lit) (.block (Jacobian.infinity Kc Kc.D)))
        (fprogB Kc.M (VG.Impl.Weierstrass.jacTail Kc.S Kc.R (Naf.twice Kc) Kc.D)) : Prog isa)).all
      (fun i => decide (dstOf i≠some .x19 ∧ dstOf i≠some .x20))=true := by decide +kernel
  intro r hr i hi
  have hh := of_decide_eq_true (List.all_eq_true.mp h i hi)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hh.1
  · exact hh.2

theorem nafTable_checks : NafTableChecks (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256) where
  double := by jac_field_ct
  copyTwice := by jac_field_ct
  copyInit := by jac_field_ct
  pointer := by jac_field_ct
  store := by jac_reg_ct [.x0,.x20]
  initCounter := by jac_reg_ct [.x0,.x20]
  add := {
    zero := by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> jac_field_ct
    copyP := by jac_field_ct
    copyQ := by jac_field_ct
    head := by jac_field_ct
    tail := by jac_field_ct
    double := Forward.rd_ct
    infinity := by jac_field_ct }
  copyStep := by jac_field_ct
  advance := by jac_reg_ct [.x19,.x20]
  keepAdd := nafTable_add_preserves

theorem nafWindow_checks : NafWindowChecks (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256) where
  tree := nafTable_checks
  treeCopy := jacTree_copy_preserves
  step := nafStep_checks
  infinity := jacWindow_infinity_ct
  counter := by jac_field_ct
  finish := jacWindow_finish_ct


theorem nafPrep_checks : NafPrepChecks (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256) (p256.sl V) where
  init := by jac_field_ct
  step := by jac_reg_ct nafPrepPublic

theorem nafVerify_checks : NafVerifyChecks p256 where
  before := jacPrefix_ct
  comb := jacComb_checks
  combFinish := jacComb_finish_ct
  save := jacSave_ct
  prep := nafPrep_checks
  window := nafWindow_checks
  tail := jacSumTail_ct

end VG.Proof.Ecdsa.Verify.AArch64
