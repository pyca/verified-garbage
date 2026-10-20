module
public import VerifiedGarbage.Proof.Framework.RelCT
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.PowerTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant-time traces of the shared IA-32 exponentiation body -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

theorem body_relCT (n e : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg t 0))
      (body n e) (fun _ _ => True) := by
  unfold body save core
  rw [List.append_assoc]
  refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) (RelCT.block_append (RelCT.seq (scratchArgument_relCT 0) ?_)) ?_
  · exact checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl
  · refine RelCT.seq (RelCT.seq
      (checkedProgramChange (contextSetup_check n) (σ := workspaceTaint false) rfl)
      (checkedProgramChange (exponentiate_check n e) (σ := workspaceTaint false) rfl)) ?_
    exact (checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) (by rfl) rfl).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Dsa.X86.Pow
