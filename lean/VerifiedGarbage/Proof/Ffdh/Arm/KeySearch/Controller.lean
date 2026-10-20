module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Native controller fields occupy the low halves of packed-u64 words.
Pointers and bounded counters are represented exactly by their ARMv7 words. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

def lowWord (m : Mem) (base : BitVec 32) (j : Nat) : BitVec 32 := m.readW (off (State.addr base) (8 * j)) 32

def writeLow (m : Mem) (base : BitVec 32) (values : List (Nat × BitVec 32)) : Mem :=
  values.foldl (fun mem e => mem.writeW (off (State.addr base) (8 * e.1)) e.2) m

structure Controller (base : BitVec 32) (s : State) : Prop where
  space : Workspace s base 128
  ptr : s.gpr .r4 = base

theorem Controller.addr {base : BitVec 32} {s : State} (h : Controller base s) {j : Nat} (fit : j < 16) :
    State.addr (s.gpr .r4 + BitVec.ofNat 32 (8 * j)) = off (State.addr base) (8 * j) := by
  rw [h.ptr]
  exact VG.Arm.addr_add (by have := h.space.nowrap; omega)

theorem Controller.read {base : BitVec 32} {s : State} (h : Controller base s) {j : Nat} (fit : j < 16) :
    InRegions (s.rd ++ s.wr) (off (State.addr base) (8 * j)) 4 := h.space.read (by omega)

theorem Controller.write {base : BitVec 32} {s : State} (h : Controller base s) {j : Nat} (fit : j < 16) :
    InRegions s.wr (off (State.addr base) (8 * j)) 4 := h.space.write (by omega)

theorem writeLow_frame (m : Mem) (base : BitVec 32) (values : List (Nat × BitVec 32))
    (bounds : ∀ e ∈ values, e.1 < 16) : Frame [⟨State.addr base, 128⟩] m (writeLow m base values) := by
  induction values generalizing m with
  | nil => exact Frame.refl _ _
  | cons e tail ih =>
    have sub : (⟨off (State.addr base) (8 * e.1), 4⟩ : Region).Sub ⟨State.addr base, 128⟩ :=
      Offset.sub_base _ (by have := bounds e (by simp); omega)
    have first : Frame [⟨State.addr base, 128⟩] m (m.writeW (off (State.addr base) (8 * e.1)) e.2) :=
      ((Frame.refl _ _).writeW (by simp : (⟨State.addr base, 128⟩ : Region) ∈ [⟨State.addr base, 128⟩]) _
        (Offset.contains_base _ (by have := bounds e (by simp); omega) (by have := bounds e (by simp); omega)))
    exact first.trans (ih _ (fun v hv => bounds v (by simp [hv])))

def lowValue (values : List (Nat × BitVec 32)) (j : Nat) (initial : BitVec 32) : BitVec 32 :=
  values.foldl (fun value e => if j = e.1 then e.2 else value) initial

theorem lowWord_store (m : Mem) (base : BitVec 32) (v : BitVec 32) {i j : Nat}
    (hi : i < 16) (hj : j < 16) :
    lowWord (m.writeW (off (State.addr base) (8 * i)) v) base j =
      if j = i then v else lowWord m base j := by
  by_cases same : j = i
  · subst j
    rw [ite_eq_left rfl]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right same]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem lowWord_writeLow (m : Mem) (base : BitVec 32) (values : List (Nat × BitVec 32))
    (bounds : ∀ e ∈ values, e.1 < 16) (j : Nat) (hj : j < 16) :
    lowWord (writeLow m base values) base j = lowValue values j (lowWord m base j) := by
  induction values generalizing m with
  | nil => rfl
  | cons e tail ih =>
    change lowWord (writeLow (m.writeW (off (State.addr base) (8 * e.1)) e.2) base tail) base j = _
    rw [ih _ (fun v hv => bounds v (List.mem_cons_of_mem _ hv)),
      lowWord_store _ _ _ (bounds e (List.mem_cons_self ..)) hj]
    rfl

theorem lowValue_unchanged (values : List (Nat × BitVec 32)) (j : Nat) (initial : BitVec 32)
    (absent : ∀ e ∈ values, j ≠ e.1) : lowValue values j initial = initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons e tail ih =>
    change lowValue tail j (if j = e.1 then e.2 else initial) = initial
    rw [ite_eq_right (absent e (List.mem_cons_self ..))]
    exact ih initial (fun v hv => absent v (List.mem_cons_of_mem _ hv))

end VG.Proof.Ffdh.Arm.KeySearch
