module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.FinishMemory
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Push

/-! The parameter search reuses the established ARMv7 24-byte saved-register frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

abbrev searchPushed (s : State) : State := pushed [.r4, .r9, .r10, .r11, .r12, .lr] s

def bodyState (s : State) : State := (searchPushed s).withRegions
  (⟨State.addr (searchPushed s).sp, 24⟩ :: s.rd) s.wr

theorem push_saved (s : State) (fit : 24 ≤ s.sp.toNat) :
    Spill.Saved (bodyState s).mem (State.addr (bodyState s).sp) s.gpr savedSlots := by
  exact VG.Proof.Ffdh.Arm.KeySearch.push_saved s fit

theorem body_writes (s : State) : Covers (bodyState s).wr (searchPushed s).wr :=
  Covers.of_mem fun _ member => List.mem_cons_of_mem _ member

theorem body_reads (s : State) :
    Covers ((bodyState s).rd ++ (bodyState s).wr) ((searchPushed s).rd ++ (searchPushed s).wr) := by
  apply Covers.of_mem
  intro r member
  change r ∈ (⟨State.addr (searchPushed s).sp, 24⟩ :: s.rd) ++ s.wr at member
  simp only [List.mem_append, List.mem_cons] at member
  rcases member with (rfl | read) | write
  · exact List.mem_append_right _ (List.mem_cons_self)
  · exact List.mem_append_left _ read
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ write)

end VG.Proof.Ffdh.Arm.ParameterSearch
