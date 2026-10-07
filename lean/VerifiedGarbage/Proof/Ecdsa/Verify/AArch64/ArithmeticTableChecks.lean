import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafChecks

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

private def arithmeticTableAddCode :=
  ArithmeticAdd.add (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256)
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).R
    (Naf.twice (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256))
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).D
materialize_value arithmeticTableAddCode

private theorem arithmeticTable_add_preserves : ∀ r∈[Reg.x19,Reg.x20],
    ∀ i∈instrs (ArithmeticAdd.add (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256)
      (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).R
      (Naf.twice (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256))
      (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256).D),dstOf i≠some r := by
  change ∀ r∈[Reg.x19,Reg.x20],∀ i∈instrs arithmeticTableAddCode,dstOf i≠some r
  rw [arithmeticTableAddCode.lit_eq]
  have h : (instrs arithmeticTableAddCode.lit).all
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
