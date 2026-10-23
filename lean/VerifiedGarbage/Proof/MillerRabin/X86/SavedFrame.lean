module

public import VerifiedGarbage.Proof.MillerRabin.X86.EntryMemory
import VerifiedGarbage.Proof.Framework.Offset

/-! # Nested-call stack writes leave the round's saved registers intact -/

@[expose] public section
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
