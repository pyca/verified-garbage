module

public import VerifiedGarbage.Proof.Mont.Words32

public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame

public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.ArgFar
import VerifiedGarbage.Proof.Mont.X86.ArgWs

/-! # Saving registers leaves the prepared workspace and arguments intact -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Entry.ws_toNat {s : State} (_ : Entry s) : (wsOf s).toNat = (arg s 0).toNat := by
  simp only [wsOf, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem Entry.headerFit {s : State} (A : Entry s) : 128 ≤ lenOf s := by
  have fit := A.layout.2.2.1
  unfold Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at fit
  unfold lenOf
  omega

theorem Entry.savedSeparate' {s : State} (A : Entry s) :
    (below (s.gpr .esp) 16).Disjoint ⟨wsOf s, lenOf s⟩ := by
  unfold below
  rw [Taint.sub_setWidth A.stackFit]
  exact A.savedSeparate

theorem Entry.pushed_read {s : State} (A : Entry s) {d bits : Nat}
    (fit : d + bits / 8 ≤ lenOf s) :
    (entered s).mem.readW (off (wsOf s) d) bits = s.mem.readW (off (wsOf s) d) bits := by
  have bound := A.bound
  have saved := pushed_frame (rs := savedRegisters) (s := s) (by decide) A.stackFit
  exact saved.readW (r := ⟨wsOf s, lenOf s⟩) (Offset.contains_base _ fit (by omega))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact A.savedSeparate'.symm) (by omega)

theorem Entry.pushed_w32 {s : State} (A : Entry s) {d : Nat} (fit : d + 4 ≤ lenOf s) :
    w32 (entered s).mem (wsOf s) d = w32 s.mem (wsOf s) d :=
  congrArg BitVec.toNat (A.pushed_read (bits := 32) fit)

theorem Entry.savedFar {s : State} (A : Entry s) : ∀ i < 4, ∀ j < 4,
    lenOf s ≤ ofs (wsOf s) (addr ((entered s).gpr .esp) (4 * i) + BitVec.ofNat 64 j) := by
  intro i hi j hj
  apply VG.Proof.Mont.X86.Dynamic.ofs_far
  intro hc
  apply A.savedSeparate' _ ?_ hc
  have fit : ((entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [entered, pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat A.stackFit]
    have := (s.gpr .esp).isLt
    omega
  have region : below (s.gpr .esp) 16 = ⟨((entered s).gpr .esp).setWidth 64, 16⟩ := by
    unfold entered savedRegisters below
    rw [pushed_esp]
    rfl
  rw [region, addr_eq (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  exact Offset.contains_base _ (by omega) (by omega)

theorem Entry.returnFar {s : State} (A : Entry s) : ∀ j < 4,
    lenOf s ≤ ofs (wsOf s) ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 j) := by
  intro j hj
  exact VG.Proof.Mont.X86.Dynamic.ofs_far fun hc =>
    A.returnSeparate _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.Mont.X86.Compact
