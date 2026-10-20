module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyConstants
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Framework.Offset

/-! Constant-table reads survive the controller's disjoint writes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyConstants
open VG VG.Arm VG.Impl.Ffdh.Arm.VettedGroups

theorem tablePtr_of_syms {sampling : GenerationPolicy} {s t : State}
    (syms : t.syms = s.syms) : tablePtr sampling t = tablePtr sampling s := by
  cases sampling with
  | full => rfl
  | vetted => exact congrFun syms tableSym

 theorem held_of_consts {sampling : GenerationPolicy} {stack : Nat} {s : State}
    (hc : ConstsOk (consts sampling) stack s) : held sampling (tablePtr sampling s) s.mem := by
  intro c member i hi
  have original := hc.2.1 c member i hi
  cases sampling with
  | full => exact False.elim (List.not_mem_nil member)
  | vetted =>
    simp only [consts, tableConsts, List.mem_singleton] at member
    subst c
    exact original

private theorem singleton_held_after_frame {name : String} {words : List (BitVec 64)}
    {ptr : BitVec 32} {m m' : Mem} {changes : List Region}
    (size : words.length < 2 ^ 60)
    (h : Abi.constsHeld m (fun _ => State.addr ptr) [(name, words)])
    (frame : Frame changes m m')
    (safe : ∀ table ∈ [(⟨State.addr ptr, 8 * words.length⟩ : Region)], ∀ r ∈ changes, table.Disjoint r) :
    Abi.constsHeld m' (fun _ => State.addr ptr) [(name, words)] := by
  intro c member i hi
  simp only [List.mem_singleton] at member
  subst c
  dsimp only [Prod.snd] at hi
  rw [frame.readW (r := ⟨State.addr ptr, 8 * words.length⟩)
    (Offset.contains_base _ (by omega) (by omega))
    (fun r hr => safe _ List.mem_cons_self r hr) (by decide)]
  exact h _ List.mem_cons_self i hi

 theorem held_after_frame {sampling : GenerationPolicy} {ptr : BitVec 32}
    {m m' : Mem} {changes : List Region} (h : held sampling ptr m)
    (frame : Frame changes m m')
    (safe : ∀ table ∈ regions sampling ptr, ∀ r ∈ changes, table.Disjoint r) :
    held sampling ptr m' := by
  cases sampling with
  | full =>
    intro c member
    exact False.elim (List.not_mem_nil member)
  | vetted =>
    exact singleton_held_after_frame (name := tableSym) (words := tableWords)
      (by rw [VG.Proof.Ffdh.Arm.VettedGroups.tableWords_length]; decide) h frame safe

end VG.Proof.Ffdh.Arm.KeyConstants
