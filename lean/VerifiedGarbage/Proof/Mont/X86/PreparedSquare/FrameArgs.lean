module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.RawArgs

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Frame
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Saved
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.ArgWs

/-! # Original cdecl arguments remain above the public cache -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem RawArgs.word {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (h : RawArgs s W L A) {i : Nat} (index : i < 5) :
    s.mem.readW (argAddr s i) 32 = A i := by
  have H := h.read i index
  change s.load32 (argAddr s i) = some (A i) at H
  unfold State.load32 at H
  split at H
  · exact Option.some.inj H
  · cases H

theorem entered_argument_address (s : State) (i : Nat) :
    (entered s).ea (Compact.arg i) = argAddr s i := by
  change (((entered s).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) = _
  rw [entered, pushed_esp, show 4 * cacheRegisters.length = 16 from rfl,
    show 20 + 4 * i = 16 + (4 + 4 * i) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem original_args {s t : State} (A : Compact.Entry s) {rs : List Reg}
    (K : Keeps rs s t) (sp : .esp ∉ rs)
    (ha : RawArgs t (Compact.wsOf s) (Compact.lenOf s) (arg s)) :
    Compact.Args (entered t) (Compact.wsOf s) (Compact.lenOf s) (arg s) := by
  have es : t.gpr .esp = s.gpr .esp := K.1 _ sp
  have addresses (i : Nat) : argAddr t i = argAddr s i := by simp only [argAddr, es]
  have fit : 16 ≤ (t.gpr .esp).toNat := by rw [es]; exact A.stackFit
  constructor
  · intro i index
    have saved := pushed_frame (rs := cacheRegisters) (s := t) (by decide) fit
    have separate : (⟨argAddr s 0, 20⟩ : Region).Disjoint (below (t.gpr .esp) 16) := by
      rw [es]
      unfold below
      rw [Taint.sub_setWidth A.stackFit]
      exact A.savedArgsSeparate.symm
    have contains : (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s i) 4 := by
      rw [Compact.argument_offset A index]
      exact Offset.contains_base _ (by omega) (by omega)
    have value : (entered t).mem.readW (argAddr s i) 32 = arg s i := by
      refine (saved.readW contains (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)).trans ?_
      rw [← addresses]
      exact ha.word index
    have access : InRegions ((entered t).rd ++ (entered t).wr) (argAddr s i) 4 := by
      rw [entered, pushed_rd, K.2.1, A.rd]
      exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), contains⟩
    change (entered t).load32 ((entered t).ea (Compact.arg i)) = _
    rw [entered_argument_address, addresses, State.load32, ite_eq_left access, value]
  · intro i index j byte
    apply Dynamic.ofs_far
    intro hc
    apply A.argSeparate _ hc
    rw [entered_argument_address, addresses, Compact.argument_offset A index, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)

theorem entered_ws {s : State} {W : Addr} {L : Nat} (hw : Ws s W L) : Ws (entered s) W L := by
  refine ⟨?_, hw.nowrap⟩
  rw [entered, pushed_wr]
  exact List.mem_cons_of_mem _ hw.1

theorem entered_read {s t : State} (A : Compact.Entry s) {rs : List Reg}
    (K : Keeps rs s t) (sp : .esp ∉ rs) {d bits : Nat} (fit : d + bits / 8 ≤ Compact.lenOf s) :
    (entered t).mem.readW (off (Compact.wsOf s) d) bits = t.mem.readW (off (Compact.wsOf s) d) bits := by
  have es := K.1 .esp sp
  have bound := A.bound
  have saved := pushed_frame (rs := cacheRegisters) (s := t) (by decide) (by rw [es]; exact A.stackFit)
  exact saved.readW (r := ⟨Compact.wsOf s, Compact.lenOf s⟩)
    (Offset.contains_base _ fit (by have := A.ws_toNat; omega))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; rw [es]; exact A.savedSeparate'.symm) (by omega)

theorem entered_w32 {s t : State} (A : Compact.Entry s) {rs : List Reg}
    (K : Keeps rs s t) (sp : .esp ∉ rs) {d : Nat} (fit : d + 4 ≤ Compact.lenOf s) :
    w32 (entered t).mem (Compact.wsOf s) d = w32 t.mem (Compact.wsOf s) d :=
  congrArg BitVec.toNat (entered_read A K sp (bits := 32) fit)

theorem entered_val32 {s t : State} (A : Compact.Entry s) {rs : List Reg}
    (K : Keeps rs s t) (sp : .esp ∉ rs) {d n : Nat} (fit : d + 4 * n ≤ Compact.lenOf s) :
    val32 (entered t).mem (Compact.wsOf s) d n = val32 t.mem (Compact.wsOf s) d n := by
  apply val32_congr
  intro i index
  exact entered_w32 A K sp (by omega)

theorem entered_metadata {s t : State} (A : Compact.Entry s) {rs : List Reg}
    (K : Keeps rs s t) (sp : .esp ∉ rs) {N S mo a b : Nat}
    (M : Compact.Metadata t.mem (Compact.wsOf s) (arg s) N S mo a b) :
    Compact.Metadata (entered t).mem (Compact.wsOf s) (arg s) N S mo a b := by
  have fit := A.headerFit
  refine ⟨?_, M.aIndex, M.bIndex, ?_, ?_, ?_, ?_⟩
  · rw [entered_w32 A K sp (by omega)]; exact M.width
  · rw [entered_w32 A K sp (by omega)]; exact M.scratch
  · rw [entered_w32 A K sp (by omega)]; exact M.modulus
  · rw [entered_w32 A K sp (by have := M.aIndex; omega)]; exact M.left
  · rw [entered_w32 A K sp (by have := M.bIndex; omega)]; exact M.right

theorem entered_saved {s t : State} (A : Compact.Entry s) {rs : List Reg}
    (K : Keeps rs s t) (sp : .esp ∉ rs) {S : Nat} {g : Reg → BitVec 32}
    (fit : S + 16 ≤ Compact.lenOf s) (saved : SavedAt t.mem (Compact.wsOf s) S g) :
    SavedAt (entered t).mem (Compact.wsOf s) S g := by
  unfold SavedAt
  rw [entered_read A K sp (by omega), entered_read A K sp (by omega),
    entered_read A K sp (by omega), entered_read A K sp (by omega)]
  exact saved

end VG.Proof.Mont.X86.PreparedSquare
