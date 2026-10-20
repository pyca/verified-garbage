module

public import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.ArgWs

/-! # The register-saving frame retains cdecl arguments and workspace access -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Mont.X86

theorem argument_address (s : State) (i : Nat) :
    (entered s).ea (Compact.arg i) = argAddr s i := by
  change (((entered s).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) = _
  rw [entered, pushed_esp, show 4 * savedRegisters.length = 16 from rfl,
    show 20 + 4 * i = 16 + (4 + 4 * i) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem argument_offset {s : State} (A : Entry s) {i : Nat} (index : i < 5) :
    argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  have bound := A.stackBound
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem Entry.pushed_arg {s : State} (A : Entry s) {i : Nat} (index : i < 5) :
    (entered s).mem.readW (argAddr s i) 32 = arg s i := by
  have saved := pushed_frame (rs := savedRegisters) (s := s) (by decide) A.stackFit
  have separate : (⟨argAddr s 0, 20⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    unfold below
    rw [Taint.sub_setWidth A.stackFit]
    exact A.savedArgsSeparate.symm
  have contains : (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s i) 4 := by
    rw [argument_offset A index]
    exact Offset.contains_base _ (by omega) (by omega)
  exact saved.readW contains (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)

theorem Entry.pushed_args {s : State} (A : Entry s) :
    Args (entered s) (wsOf s) (lenOf s) (arg s) := by
  constructor
  · intro i index
    change (entered s).load32 ((entered s).ea (Compact.arg i)) = _
    rw [argument_address]
    have access : InRegions ((entered s).rd ++ (entered s).wr) (argAddr s i) 4 := by
      rw [entered, pushed_rd, A.rd]
      refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
      rw [argument_offset A index]
      exact Offset.contains_base _ (by omega) (by omega)
    rw [State.load32, ite_eq_left access, A.pushed_arg index]
  · intro i index j byte
    apply VG.Proof.Mont.X86.Dynamic.ofs_far
    intro hc
    apply A.argSeparate _ hc
    rw [argument_address, argument_offset A index, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)

theorem Entry.pushed_ws {s : State} (A : Entry s) : Ws (entered s) (wsOf s) (lenOf s) := by
  refine ⟨?_, ?_⟩
  · rw [entered, pushed_wr, A.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · rw [A.ws_toNat]; exact A.bound

end VG.Proof.Mont.X86.Compact
