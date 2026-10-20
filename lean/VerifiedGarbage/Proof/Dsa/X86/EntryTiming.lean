module

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Entry and return traces depend only on caller stack and scratch addresses -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86

def entryTaint : VG.X86.Taint.T := { regs := .ofList [.esp, .edi], flags := false }
def scratchArgumentTaint : VG.X86.Taint.T := { regs := .ofList [.esp, .eax], flags := false }
def stackTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false }

theorem scratchArgument_relCT (i : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s i = stackValue t i ∧
      readSrc s (.mem (Entry.argument i)) = some (stackValue s i) ∧
      readSrc t (.mem (Entry.argument i)) = some (stackValue t i))
      (.block [.mov .eax (.mem (Entry.argument i))]) (VG.X86.Taint.Agree scratchArgumentTaint) := by
  intro s t tr ur sf tf ⟨SP, V, S, T⟩ E F
  have A := agree_regs (rs := [.esp]) (fun reg hr => by obtain rfl := List.mem_singleton.mp hr; exact SP)
  have check : VG.Taint.check taint stackTaint (.block [.mov .eax (.mem (Entry.argument i))]) (.block []) = some stackTaint := by
    change taint.checkBlock stackTaint [.mov .eax (.mem (Entry.argument i))] = some stackTaint
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases stackTaint = true from rfl)]
    change taint.checkBlock stackTaint [.mov .eax (.mem (Entry.argument i))] = _
    have H : VG.X86.Taint.loadPubK stackTaint (.mem (Entry.argument i)) = false := by
      rw [VG.X86.Taint.loadPubK_eq]
      change VG.X86.Taint.argPub stackTaint (Entry.argument i) 4 = false
      simp [VG.X86.Taint.argPub, stackTaint, Entry.argument, at_, VG.X86.Taint.depth]
    simp only [VG.Taint.checkBlock, taint, VG.X86.Taint.stepKD, VG.X86.Taint.stepKDFn]
    have MB : VG.X86.Taint.movBasesK stackTaint .eax (.mem (Entry.argument i)) = [] := by
      rw [VG.X86.Taint.movBasesK_eq]
      simp [VG.X86.Taint.movBases, VG.X86.Taint.loadBases, VG.X86.Taint.addrOf, VG.X86.Taint.kill, stackTaint]
    rw [H, MB]
    simp only [VG.X86.Taint.srcOkK, VG.X86.Taint.srcPub, Entry.argument, at_]
    rfl
  have first {s : State} (H : readSrc s (.mem (Entry.argument i)) = some (stackValue s i)) :
      WP isa (.block [.mov .eax (.mem (Entry.argument i))]) s fun t =>
        t.gpr .eax = stackValue s i ∧ Keeps [.eax] s t :=
    wp_movS H fun t U _ => WP.block_nil ⟨U.gpr, U.keeps⟩
  obtain ⟨V1, K1⟩ := wp_result (first S) E
  obtain ⟨V2, K2⟩ := wp_result (first T) F
  refine ⟨(VG.Taint.check_sound check A E F).1, ?_⟩
  apply agree_regs (rs := [.esp, .eax])
  intro reg hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [K1.1 _ (by decide), K2.1 _ (by decide)]; exact SP
  · exact V1.trans (V.trans V2.symm)

theorem openScratch_relCT (i : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s i = stackValue t i ∧
      readSrc s (.mem (Entry.argument i)) = some (stackValue s i) ∧
      readSrc t (.mem (Entry.argument i)) = some (stackValue t i))
      (.block (Entry.openScratch i)) (VG.X86.Taint.Agree entryTaint) := by
  unfold Entry.openScratch
  rw [List.append_assoc]
  apply RelCT.block_append
  exact RelCT.seq (scratchArgument_relCT i)
    (checkedProgramChange (τ' := { entryTaint with regs := .ofList [.esp, .edi, .eax] }) (hint := .block []) rfl rfl)

theorem saveArgument_relCT (i : Nat) (f : VG.Impl.Dsa.Layout.Field) :
    RelCT isa (VG.X86.Taint.Agree entryTaint) (.block (Entry.saveArgument i f)) (VG.X86.Taint.Agree entryTaint) := by
  apply checkedBlockInvariant (τ' := entryTaint) ?_ rfl
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases entryTaint = true from rfl)]
  change taint.checkBlock entryTaint [.mov .eax (.mem (Entry.argument i)), .store (sc 0) .eax] = _
  have H : VG.X86.Taint.loadPubK entryTaint (.mem (Entry.argument i)) = false := by
    rw [VG.X86.Taint.loadPubK_eq]
    change VG.X86.Taint.argPub entryTaint (Entry.argument i) 4 = false
    simp [VG.X86.Taint.argPub, entryTaint, Entry.argument, at_, VG.X86.Taint.depth]
  simp only [VG.Taint.checkBlock, taint, VG.X86.Taint.stepKD, VG.X86.Taint.stepKDFn]
  have MB : VG.X86.Taint.movBasesK entryTaint .eax (.mem (Entry.argument i)) = [] := by
    rw [VG.X86.Taint.movBasesK_eq]
    simp [VG.X86.Taint.movBases, VG.X86.Taint.loadBases, VG.X86.Taint.addrOf, VG.X86.Taint.kill, entryTaint]
  rw [H, MB]
  simp only [VG.X86.Taint.srcOkK, VG.X86.Taint.srcPub, Entry.argument, at_]
  rfl

theorem saveArguments_relCT (args : List (Nat × VG.Impl.Dsa.Layout.Field)) :
    RelCT isa (VG.X86.Taint.Agree entryTaint) (.block (Entry.saveArguments args)) (VG.X86.Taint.Agree entryTaint) :=
  blockFlatMap_relCT args _ (fun a => saveArgument_relCT a.1 a.2)

theorem installEntry_relCT (i : Nat) (args : List (Nat × VG.Impl.Dsa.Layout.Field)) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s i = stackValue t i ∧
      readSrc s (.mem (Entry.argument i)) = some (stackValue s i) ∧
      readSrc t (.mem (Entry.argument i)) = some (stackValue t i))
      (.block (Entry.openScratch i ++ Entry.saveArguments args ++ Entry.keyPointers))
      (VG.X86.Taint.Agree entryTaint) :=
  RelCT.block_append (RelCT.seq (RelCT.block_append (RelCT.seq
    (openScratch_relCT i) (saveArguments_relCT args))) (checkedBlockInvariant (τ' := entryTaint) rfl rfl))

theorem restore_relCT : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
    (.block Entry.restore) (fun _ _ => True) := by
  exact RelCT.taint (A := taint) (workspaceTaint false) (fun _ _ h => h) (hc := .block []) rfl

end VG.Proof.Dsa.X86
