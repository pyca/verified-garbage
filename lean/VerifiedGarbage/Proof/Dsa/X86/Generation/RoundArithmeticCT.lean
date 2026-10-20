module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.ChecksTiming
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Round
public import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreSetupTiming
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.ChecksTiming
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Montgomery powers, residue squares, and comparisons have fixed schedules -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

theorem ordinarySquare_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (ordinarySquare n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold ordinarySquare
  exact RelCT.seq (checkedProgramChange (mul_check false _ _ _ _ _ _) rfl)
    (checkedProgramChange (mul_check false _ _ _ _ _ _) rfl)

theorem roundCompare_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (roundCompare n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold roundCompare
  exact RelCT.seq (equal_relCT false _ _ _)
    (RelCT.seq (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl)
      (RelCT.seq (equal_relCT false _ _ _)
        (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl)))

theorem roundSquare_ct (n : Nat) : RelCT isa (RegistersAgree [.edi]) (roundSquare n) (fun _ _ => True) := by
  unfold roundSquare
  exact (RelCT.seq (ordinarySquare_relCT n) (roundCompare_relCT n)).mono
    (fun _ _ h => agree_regs h) (fun _ _ _ => trivial)

theorem roundMinusOne_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (roundMinusOne n)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  erased_relCT _ (roundMinusOne 1)
    (VG.Taint.hintOf taint (workspaceTaint false) (Code.erase (roundMinusOne 1))) rfl rfl rfl rfl

theorem roundMinusOne_ct (n : Nat) : RelCT isa (RegistersAgree [.edi]) (roundMinusOne n) (fun _ _ => True) :=
  (roundMinusOne_relCT n).mono (fun _ _ h => agree_regs h) (fun _ _ _ => trivial)

theorem exponentiate_ct (n expWords : Nat) :
    RelCT isa (RegistersAgree [.edi]) (exponentiate n expWords) (fun _ _ => True) :=
  (checkedProgramChange (exponentiate_check n expWords)
    (show taint.le (workspaceTaint false) (rowTaint false) = true from rfl)).mono
    (fun _ _ h => agree_regs h) (fun _ _ _ => trivial)

theorem contextSetup_ct (n : Nat) : RelCT isa (RegistersAgree [.edi]) (contextSetup n) (fun _ _ => True) :=
  (contextSetup_relCT n).mono (fun _ _ h => agree_regs h) (fun _ _ _ => trivial)
end VG.Proof.Dsa.X86.Generation
