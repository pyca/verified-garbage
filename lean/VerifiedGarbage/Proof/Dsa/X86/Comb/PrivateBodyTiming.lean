module

import VerifiedGarbage.Proof.Dsa.X86.Comb.Correct
import VerifiedGarbage.Proof.Dsa.X86.Comb.PrivateTiming
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! The callable private comb helper leaks no exponent-dependent trace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem save_relCT :
    RelCT isa (fun s t => s.gpr .esp=t.gpr .esp ∧ arg s 0=arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg t 0))
      (.block VG.Impl.Dsa.X86.Pow.save) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Dsa.X86.Pow.save
  rw [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (scratchArgument_relCT 0)
    (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl))

theorem private_body_relCT {n e : Nat} (h : Supported n e) :
    RelCT isa (fun s t => s.gpr .esp=t.gpr .esp ∧ arg s 0=arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg t 0))
      (body false n e) (fun _ _ => True) := by
  unfold body
  refine RelCT.seq save_relCT ?_
  have eq : privateInputs=workspaceTaint false := by decide
  rw [←eq]
  refine RelCT.seq (private_core_relCT h) ?_
  exact (checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) rfl rfl).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Dsa.X86.Comb
