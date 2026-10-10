import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafChecks

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

private abbrev Kc := VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256

/-- The forwarded blocks of the table addition are the Forward framework's
literals, so the kernel never runs the optimizer here. -/
private theorem head_lit : VG.Impl.P256.VerifyArithmetic.program Kc.M (VG.Impl.Weierstrass.jacHead Kc.S Kc.R (Naf.twice Kc)) =
    .block Forward.ArithmeticTableHead.rightCode.lit := by
  have hs : VG.Impl.P256.VerifyArithmetic.selected VG.Impl.P256.VerifyDouble.M
      (VG.Impl.P256.VerifyArithmetic.operations .tableHead) :=
    ⟨rfl,List.mem_map.mpr ⟨.tableHead,by simp [VG.Impl.P256.VerifyArithmetic.kinds],rfl⟩⟩
  change VG.Impl.P256.VerifyArithmetic.program VG.Impl.P256.VerifyDouble.M
    (VG.Impl.P256.VerifyArithmetic.operations .tableHead) = _
  rw [VG.Impl.P256.VerifyArithmetic.program,ite_eq_left hs]
  exact congrArg Code.block Forward.ArithmeticTableHead.optimized_lit

private theorem tail_lit : VG.Impl.P256.VerifyArithmetic.program Kc.M (VG.Impl.Weierstrass.jacTail Kc.S Kc.R (Naf.twice Kc) Kc.D) =
    .block Forward.ArithmeticTableTail.rightCode.lit := by
  have hs : VG.Impl.P256.VerifyArithmetic.selected VG.Impl.P256.VerifyDouble.M
      (VG.Impl.P256.VerifyArithmetic.operations .tableTail) :=
    ⟨rfl,List.mem_map.mpr ⟨.tableTail,by simp [VG.Impl.P256.VerifyArithmetic.kinds],rfl⟩⟩
  change VG.Impl.P256.VerifyArithmetic.program VG.Impl.P256.VerifyDouble.M
    (VG.Impl.P256.VerifyArithmetic.operations .tableTail) = _
  rw [VG.Impl.P256.VerifyArithmetic.program,ite_eq_left hs]
  exact congrArg Code.block Forward.ArithmeticTableTail.optimized_lit

private theorem arithmeticTable_add_preserves : ∀ r∈[Reg.x19,Reg.x20],
    ∀ i∈instrs (ArithmeticAdd.add Kc Kc.R (Naf.twice Kc) Kc.D),dstOf i≠some r := by
  rw [ArithmeticAdd.add,head_lit,tail_lit,jacWinCfg_double_lit]
  have h : (instrs (.seq (.block (zeroMask Kc.M.n Kc.R.z)) <|
      .ite (.nonzero .x .x2) (.block (copyPt Kc.M.n Kc.D (Naf.twice Kc))) <|
      .seq (.block (zeroMask Kc.M.n (Naf.twice Kc).z)) <|
      .ite (.nonzero .x .x2) (.block (copyPt Kc.M.n Kc.D Kc.R)) <|
      .seq (.block Forward.ArithmeticTableHead.rightCode.lit) <|
      .seq (.block (zeroMask Kc.M.n Kc.S.t3)) <|
      .ite (.nonzero .x .x2)
        (.seq (.block (zeroMask Kc.M.n Kc.S.t5)) <|
          .ite (.nonzero .x .x2) (.block Forward.P256Bounds.rightRD.lit) (.block (Jacobian.infinity Kc Kc.D)))
        (.block Forward.ArithmeticTableTail.rightCode.lit) : Prog isa)).all
      (fun i => decide (dstOf i≠some .x19 ∧ dstOf i≠some .x20))=true := by decide +kernel
  intro r hr i hi
  have hh := of_decide_eq_true (List.all_eq_true.mp h i hi)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hh.1
  · exact hh.2

theorem arithmeticTable_checks : ArithmeticTableChecks (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256) where
  base := nafTable_checks
  add := {
    zero := nafTable_checks.add.zero
    copyP := nafTable_checks.add.copyP
    copyQ := nafTable_checks.add.copyQ
    head := Forward.ArithmeticTableHead.ct
    tail := Forward.ArithmeticTableTail.ct
    double := nafTable_checks.add.double
    infinity := nafTable_checks.add.infinity }
  keepAdd := arithmeticTable_add_preserves

end VG.Proof.Ecdsa.Verify.AArch64
