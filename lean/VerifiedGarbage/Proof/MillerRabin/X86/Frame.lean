module

public import VerifiedGarbage.Proof.MillerRabin.X86.EntryCore

import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MillerRabin.X86.EntryArgs
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.MillerRabin.X86.EntryMemory
/-! # The prepared round restores the i686 ABI after its nested calls -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/BodyFrame.lean`, which only this module imported.
section

/-! # Nested calls write below the saved i686 register frame -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86

theorem Entry.body {s : State} (E : Entry s) :
    WP isa (body montName montCode) (entered s) fun t =>
      Result s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (entered s) t ∧
      Frame ([⟨wsOf s, lenOf s⟩] ++ [below ((entered s).gpr .esp) 80]) (entered s).mem t.mem := by
  have writable : Covers [⟨wsOf s, lenOf s⟩] (entered s).wr := by
    apply Covers.of_mem
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    rw [entered, Compact.entered, pushed_wr, E.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  refine WP.narrowSp E.narrowed_body ?_ writable body_noSp ?_ ?_
  · exact Covers.append (Covers.refl _) writable
  · have := E.caller.low
    exact Nat.le_trans body_stack this
  · intro t rd wr F R
    refine ⟨R.1, ⟨R.2.1, rd, wr⟩, ?_⟩
    apply F.sub
    intro r mem
    rcases List.mem_append.mp mem with mem | mem
    · exact ⟨r, List.mem_append_left _ mem, fun _ h => h⟩
    · obtain rfl := List.mem_singleton.mp mem
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub body_stack E.caller.low⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/SavedFrame.lean`, which only this module imported.
section

/-! # Nested-call stack writes leave the round's saved registers intact -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def savedRegion (s : State) : Region := ⟨((entered s).gpr .esp).setWidth 64, 16⟩

theorem savedRegion_eq (s : State) : savedRegion s = below (s.gpr .esp) 16 := by
  unfold savedRegion entered Compact.entered
  rw [pushed_esp]
  rfl

theorem Entry.saved_stack_far {s : State} (E : Entry s) :
    (savedRegion s).Disjoint (below ((entered s).gpr .esp) 80) := by
  have low := E.stackFit
  have innerLow : 80 ≤ ((entered s).gpr .esp).toNat := by
    rw [entered, Compact.entered, pushed_esp]
    change 80 ≤ (s.gpr .esp - 16#32).toNat
    rw [sub_toNat (by omega)]
    omega
  unfold savedRegion below
  rw [Taint.sub_setWidth innerLow]
  exact Offset.base_disjoint_below _ (by decide : 16 + 80 ≤ 2 ^ 64)

theorem Entry.saved_read {s t : State} (E : Entry s)
    (F : Frame ([⟨wsOf s, lenOf s⟩] ++ [below ((entered s).gpr .esp) 80]) (entered s).mem t.mem)
    {i : Nat} (index : i < 4) :
    t.mem.readW (addr ((entered s).gpr .esp) (4 * i)) 32 =
      s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
  have low := E.stackFit
  have fit : ((entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [entered, Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat (by omega)]
    have := (s.gpr .esp).isLt
    omega
  have contained : (savedRegion s).Contains (addr ((entered s).gpr .esp) (4 * i)) 4 := by
    rw [addr_eq (by omega)]
    exact Offset.contains_base _ (by omega) (by omega)
  have same := F.readW (r := savedRegion s) (w := 32) contained (by
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · rw [savedRegion_eq]; exact E.savedSeparate
    · exact E.saved_stack_far) (by decide : 32 / 8 < 2 ^ 64)
  exact same.trans (pushed_word (rs := Compact.savedRegisters) (by decide) (by change 16 ≤ _; omega) index)

theorem Entry.return_read {s t : State} (E : Entry s)
    (F : Frame ([⟨wsOf s, lenOf s⟩] ++ [below ((entered s).gpr .esp) 80]) (entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have sub : Region.Sub (below ((entered s).gpr .esp) 80) (below (s.gpr .esp) 96) := by
    rw [entered, Compact.entered, pushed_esp]
    exact below_inner (by decide : 80 + 16 ≤ 96) E.stackFit
  have outside : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 96) := by
    unfold below
    rw [Taint.sub_setWidth E.stackFit]
    exact Offset.base_disjoint_below _ (by decide : 4 + 96 ≤ 2 ^ 64)
  have same := F.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4) (by
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact E.returnSeparate
    · exact outside.sub_right sub) (by decide : 32 / 8 < 2 ^ 64)
  have saved := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide)
    (by change 16 ≤ _; have := E.stackFit; omega)
  refine same.trans (saved.readW (Region.contains_self _ _) ?_ (by decide))
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact outside.sub_right (below_sub (by decide) E.stackFit)

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86

theorem inner_noSp : NoSp (.seq (body montName montCode) (.block VG.Impl.Mont.X86.Compact.restoreRegs)) :=
  .of_all (by decide +kernel)

theorem Result.keep {s t u : State} (R : Result s t)
    (eax : u.gpr .eax = t.gpr .eax) (mem : u.mem = t.mem) : Result s u := by
  unfold Result at *
  rw [eax, mem]
  exact R

theorem Entry.framed {s : State} (E : Entry s) :
    WP isa (code montName montCode) s fun t => abiPreserved s t ∧ Result s t := by
  unfold code
  refine WP.frame (rs := Compact.savedRegisters) (by decide) (by decide) (by decide)
    (by change 16 ≤ _; have := E.stackFit; omega) inner_noSp ?_
  refine WP.seq (WP.mono E.body fun t ⟨R, K, F⟩ => ?_)
  have sp : t.gpr .esp = (entered s).gpr .esp := K.1 .esp (by decide)
  have fit : ((entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [entered, Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat (by have := E.stackFit; omega)]
    have := (s.gpr .esp).isLt
    omega
  have read (i : Nat) (index : i < 4) :
      readSrc t (.mem (at_ .esp (4 * i))) = some
        (s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
    have access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp, entered, Compact.entered, pushed_wr]
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      rw [← savedRegion_eq]
      change (savedRegion s).Contains (addr ((entered s).gpr .esp) (4 * i)) 4
      rw [addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, sp, E.saved_read F index]
  refine WP.mono (Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro u ⟨edi, esi, ebp, mem, keep⟩
  have sp' : u.gpr .esp = (entered s).gpr .esp := (keep.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show Compact.savedRegisters.length = 4 from rfl, Compact.popped_four_value, sp', mem]
      exact E.saved_read F (by decide : 3 < 4)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', entered, Compact.entered, pushed_esp]
      exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]
    exact E.return_read F
  · apply R.keep
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact keep.1 .eax (by decide)
    · rw [popped_mem, mem]

end VG.Proof.MillerRabin.X86
