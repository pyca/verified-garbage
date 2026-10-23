module

public import VerifiedGarbage.Proof.MillerRabin.X86.Entry
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Saving the round's registers preserves its prepared workspace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

abbrev entered (s : State) : State := Compact.entered s

theorem Entry.stackSeparate' {s : State} (E : Entry s) :
    (below (s.gpr .esp) 96).Disjoint ⟨wsOf s, lenOf s⟩ := by
  unfold below
  rw [Taint.sub_setWidth E.stackFit]
  exact E.stackSeparate

theorem Entry.stackArgsSeparate' {s : State} (E : Entry s) :
    (below (s.gpr .esp) 96).Disjoint ⟨argAddr s 0, 8⟩ := by
  unfold below
  rw [Taint.sub_setWidth E.stackFit]
  exact E.stackArgsSeparate

theorem Entry.savedSeparate {s : State} (E : Entry s) :
    (below (s.gpr .esp) 16).Disjoint ⟨wsOf s, lenOf s⟩ :=
  E.stackSeparate'.sub_left (below_sub (by decide) E.stackFit)

theorem Entry.pushed_read {s : State} (E : Entry s) {d bits : Nat}
    (fit : d + bits / 8 ≤ lenOf s) :
    (entered s).mem.readW (off (wsOf s) d) bits = s.mem.readW (off (wsOf s) d) bits := by
  have bound := E.bound
  have saved := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) (by change 16 ≤ (s.gpr .esp).toNat; have := E.stackFit; omega)
  exact saved.readW (r := ⟨wsOf s, lenOf s⟩) (Offset.contains_base _ fit (by omega))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact E.savedSeparate.symm) (by omega)

theorem Entry.pushed_w32 {s : State} (E : Entry s) {d : Nat} (fit : d + 4 ≤ lenOf s) :
    w32 (entered s).mem (wsOf s) d = w32 s.mem (wsOf s) d :=
  congrArg BitVec.toNat (E.pushed_read (bits := 32) fit)

theorem Entry.pushed_val32 {s : State} (E : Entry s) {d n : Nat}
    (fit : d + 4 * n ≤ lenOf s) :
    val32 (entered s).mem (wsOf s) d n = val32 s.mem (wsOf s) d n := by
  apply val32_congr
  intro i index
  exact E.pushed_w32 (by omega)

end VG.Proof.MillerRabin.X86
