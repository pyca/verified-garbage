module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.Checks
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare
import VerifiedGarbage.Proof.Ffdh.Arm.ChecksCT
meta import VerifiedGarbage.Proof.Ffdh.Arm.ChecksCT

/-! Testing zero and one uses fixed-width arithmetic without value-dependent branches. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

theorem isOne_ct {base : BitVec 32} {len w a : Nat} (ha : Operand a) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.isOne a) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.isOne
  exact relCT_chain (smallConst_ct (base := base) (len := len) (w := w) 1
    (by decide : 7 < 8) (by decide) (by decide))
    (fun s h => WP.mono (smallConst_ok s 1 h (by decide : 7 < 8) (by decide) (by decide) (by decide)) fun _ k => k.1)
    (fun s h => WP.mono (smallConst_ok s 1 h (by decide : 7 < 8) (by decide) (by decide) (by decide)) fun _ k => k.1)
    (equal_ct ha (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]))

theorem negateFlag_ct : RelCT isa (fun _ _ => True)
    (.block [.dp .eor .r11 .r11 (.imm 1)]) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

theorem nonzero_ct {base : BitVec 32} {len w a : Nat} (ha : Operand a) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.nonzero a) (fun _ _ => True) := by
  have wp (s : State) (h : ArithmeticReady base len w s) :=
    WP.mono (smallConst_ok s 1 h (by decide : 7 < 8) (by decide) (by decide) (by decide)) fun _ k => k.1
  have tail := ((compare_ct (base := base) (len := len) (w := w) ha.1 (by decide : 7 < 8)).seq negateFlag_ct)
  unfold VG.Impl.Ffdh.Arm.nonzero
  exact relCT_chain (smallConst_ct (base := base) (len := len) (w := w) 1
    (by decide : 7 < 8) (by decide) (by decide)) wp wp tail

end VG.Proof.Ffdh.Arm
