module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundArithmeticCT
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SampleWitness
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.ChecksTiming
import VerifiedGarbage.Proof.Dsa.X86.ValidationBlocksTiming
public import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundArithmeticCT
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Loading and classifying a witness has a fixed arithmetic schedule -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

theorem testWitness_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (testWitness n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold testWitness
  exact RelCT.seq (lessThan_relCT false _ _ _)
    (RelCT.seq (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl)
      (RelCT.seq (lessThanConstant_relCT _ _ _ _) (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl)))

theorem sampleHead_ct (len : Nat) : RelCT isa (RegistersAgree [.edi, .esi]) (sampleHead len) (fun _ _ => True) := by
  unfold sampleHead
  refine (RelCT.seq (loadComponent_relCT _ _ _) ((RelCT.seq (roundMinusOne_relCT _) (testWitness_relCT _)).mono
    (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h))).mono (fun _ _ h => agree_regs h) (fun _ _ _ => trivial)

theorem forceSample_ct (len : Nat) : RelCT isa (RegistersAgree [.edi, .esi])
    (.seq (.block (forceWitness len)) (VG.Impl.Dsa.X86.loadComponent len ((len + 7) / 8)
      (VG.Impl.Mont.X86.Dynamic.slot ((len + 7) / 8) 5))) (fun _ _ => True) := by
  have force : RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (.block (forceWitness len))
      (VG.X86.Taint.Agree (workspaceTaint true)) :=
    erased_relCT _ (.block (forceWitness 1)) (.block []) rfl rfl rfl rfl
  exact (RelCT.seq force (loadComponent_relCT _ _ _)).mono (fun _ _ h => agree_regs h) (fun _ _ _ => trivial)
end VG.Proof.Dsa.X86.Generation
