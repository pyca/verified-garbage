module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchControlMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.WorkspaceToFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameToWorkspace
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStatus
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchSlots
import VerifiedGarbage.Proof.Mont.Words32

/-! # Copy the bounded-search offset in and return the candidate status to its controller -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem pAttemptOffset_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State} {counter stride : Nat}
    (R : SearchContext P W s) (C : SearchControl (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) counter stride s) :
    WP isa (.block pAttemptOffset) s fun t =>
      SearchContext P (frameUpdate W 2 (BitVec.ofNat 32 (1 + counter * stride))) t ∧
      ControlValues P.geometry counter stride t.mem ∧
      Frame [⟨P.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  have copy := workspaceToFrame_ok R.arena.frame C.scr R.representation (by decide : 2 < 37) (by decide : 4 + 4 ≤ 12)
  change WP isa (.block pAttemptOffset) s _ at copy
  refine WP.mono copy fun t ⟨_, _, rep, _, O, K⟩ => ?_
  rw [C.offset] at rep
  have F := searchSlot_frame (P := P) (by decide : 2 < 37) O
  exact ⟨R.slot (by decide) (by decide) rep O K (by decide),
    (ControlValues.mk C.count C.offset).frame F (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact (P.geometry.frame_part (by unfold VG.Impl.Dsa.Generation.Layout.control usedBytes domainCheck; omega : VG.Impl.Dsa.Generation.Layout.control + 8 ≤ usedBytes P.geometry.pLen)).symm), F, K⟩

theorem pAttemptReturn_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State} {counter stride : Nat}
    (R : SearchContext P W s) (C : ControlValues P.geometry counter stride s.mem) :
    WP isa (.block pAttemptReturn) s fun t =>
      SearchContext P W t ∧ SearchControl (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) counter stride t ∧
      t.mem.readW (off (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) 8) 32 = W 19 ∧
      Outside (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) 0 12 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  have parent : s.mem.readW (off P.geometry.frameBase 20) 32 = P.geometry.parent :=
    (R.representation 5 (by decide)).trans ((R.fixed 5 (by decide) (by decide)).trans P.parent)
  unfold pAttemptReturn
  change WP isa (.block (bufferPointer .edi VG.Impl.Dsa.Generation.Layout.control ++ _)) s _
  refine WP.block_append (WP.mono (bufferPointer_ok R.arena.frame parent .edi VG.Impl.Dsa.Generation.Layout.control) fun a ⟨di, mem, Ka⟩ => ?_)
  have Ra := R.congr mem Ka (by decide)
  have S := Ra.arena.controlScr di
  have copy := frameToWorkspace_ok Ra.arena.frame S Ra.representation (by decide : 19 < 37) (by decide : 8 + 4 ≤ 12)
    (P.geometry.frame_part (by unfold VG.Impl.Dsa.Generation.Layout.control usedBytes domainCheck; omega))
  refine WP.mono copy fun t ⟨_, St, _, mt, Ot, Kt⟩ => ?_
  have O : Outside (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) 0 12 s.mem t.mem := by rw [← mem]; exact Ot.mono (by omega) (by omega)
  have K : Keeps [.eax, .edi] s t := (Ka.mono (by decide)).trans (Kt.mono (by decide))
  have fixed (d : Nat) (hd : d + 4 ≤ 8) : t.mem.readW (off (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) d) 32 =
      s.mem.readW (off (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) d) 32 := by
    rw [← mem]
    apply BitVec.eq_of_toNat_eq
    exact Ot.w32 (.inl hd) (by omega)
  exact ⟨R.control O K (by decide), ⟨St, (fixed 0 (by decide)).trans C.count, (fixed 4 (by decide)).trans C.offset⟩,
    by rw [mt, Mem.readW_writeW_self32], O, K⟩
end VG.Proof.Dsa.X86.Generation
