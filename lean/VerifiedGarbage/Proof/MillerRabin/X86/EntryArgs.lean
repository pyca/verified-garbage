module

public import VerifiedGarbage.Proof.MillerRabin.X86.EntryMemory
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! # The saved round frame retains the two public cdecl arguments -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem argument_offset {s : State} (E : Entry s) {i : Nat} (index : i < 2) :
    argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  have bound := E.stackBound
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem Entry.pushed_arg {s : State} (E : Entry s) {i : Nat} (index : i < 2) :
    (entered s).mem.readW (argAddr s i) 32 = arg s i := by
  have saved := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide)
    (by change 16 ≤ (s.gpr .esp).toNat; have := E.stackFit; omega)
  have separate : (⟨argAddr s 0, 8⟩ : Region).Disjoint (below (s.gpr .esp) 16) :=
    E.stackArgsSeparate'.symm.sub_right (below_sub (by decide) E.stackFit)
  have contains : (⟨argAddr s 0, 8⟩ : Region).Contains (argAddr s i) 4 := by
    rw [argument_offset E index]
    exact Offset.contains_base _ (by omega) (by omega)
  exact saved.readW contains (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)

theorem Entry.read_arg {s : State} (E : Entry s) {i : Nat} (index : i < 2) :
    readSrc (entered s) (.mem (VG.Impl.Mont.X86.Compact.arg i)) = some (arg s i) := by
  change (entered s).load32 ((entered s).ea (VG.Impl.Mont.X86.Compact.arg i)) = _
  rw [Compact.argument_address]
  have access : InRegions ((entered s).rd ++ (entered s).wr) (argAddr s i) 4 := by
    rw [entered, Compact.entered, pushed_rd, E.rd]
    refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
    rw [argument_offset E index]
    exact Offset.contains_base _ (by omega) (by omega)
  rw [State.load32, ite_eq_left access, E.pushed_arg index]

theorem lengthRegion_entered (s : State) :
    lengthRegion ((entered s).gpr .esp) = ⟨argAddr s 1, 4⟩ := by
  change (⟨(((entered s).gpr .esp) + 24#32).setWidth 64, 4⟩ : Region) = _
  rw [entered, Compact.entered, pushed_esp]
  change (⟨(s.gpr .esp - 16#32 + (16#32 + 8#32)).setWidth 64, 4⟩ : Region) = _
  rw [← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem Entry.length_sub {s : State} (E : Entry s) :
    Region.Sub (lengthRegion ((entered s).gpr .esp)) ⟨argAddr s 0, 8⟩ := by
  rw [lengthRegion_entered, argument_offset E (by decide : 1 < 2)]
  intro x hx
  apply Region.Contains.byte (Offset.contains_base (argAddr s 0) (by decide : 4 + 4 ≤ 8) (by decide))
  change (x - (argAddr s 0 + BitVec.ofNat 64 4)).toNat + 1 ≤ 4 at hx
  omega

theorem Entry.caller {s : State} (E : Entry s) :
    Caller (geometry s) (arg s 1).toNat ((entered s).gpr .esp) (entered s) := by
  have sub : Region.Sub (below ((entered s).gpr .esp) 40) (below (s.gpr .esp) 56) := by
    rw [entered, Compact.entered, pushed_esp]
    exact below_inner (by decide : 40 + 16 ≤ 56) E.stackFit
  refine ⟨rfl, ?_, E.stackSeparate'.symm.sub_right sub,
    E.argSeparate.symm.sub_left E.length_sub, E.stackArgsSeparate'.symm.sub_left E.length_sub |>.sub_right sub, ?_⟩
  · rw [entered, Compact.entered, pushed_esp]
    change 40 ≤ (s.gpr .esp - 16#32).toNat
    rw [sub_toNat (by have := E.stackFit; omega)]
    have := E.stackFit
    omega
  · change readSrc (entered s) (.mem (VG.Impl.Mont.X86.Compact.arg 1)) = some (BitVec.ofNat 32 (arg s 1).toNat)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact E.read_arg (by decide : 1 < 2)

end VG.Proof.MillerRabin.X86
