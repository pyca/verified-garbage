module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.RandomContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateCall
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateOutgoing
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateResources

/-! # Reserve outgoing arguments, check the domain, and restore the persistent search frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem validateFrame_ok (F : KeyRandom.CheckCall.CheckFn) {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State}
    (R : SearchContext P W s) (regs : ValidateRegs P.geometry s) :
    WP isa (.frame (.alloc 24) (.seq (.block validateOutgoing) (.call F.name F.code)) (.free 24)) s fun t =>
      SearchContext P W t ∧ t.gpr .eax = (if validateResult P.geometry s.mem then 1 else 0) ∧
      Frame (validateWrites P.geometry) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have stack := P.geometry.stackSize
  have noSp : NoSp (.seq (.block validateOutgoing) (.call F.name F.code)) := by
    have outgoing : NoSp (.block validateOutgoing) := NoSp.of_all (by decide +kernel)
    intro i hi
    change i ∈ validateOutgoing ++ instrs F.code at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact outgoing i hi
    · exact F.noSp i hi
  refine WP.alloc (by decide) (by rw [R.arena.frameReg]; omega) noSp ?_
  have allocsp : (allocated 24 s).gpr .esp = P.geometry.frame - 24#32 := by rw [allocated_esp, R.arena.frameReg]
  have allocwr : (⟨validateArgsBase P.geometry, 24⟩ : Region) ∈ (allocated 24 s).wr := by
    rw [allocated_wr, R.arena.frameReg]; exact List.mem_cons_self
  have allocregs : ValidateRegs P.geometry (allocated 24 s) := by
    intro i hi
    rw [allocated_gpr 24 s (show validateReg i ≠ .esp from by
      unfold validateReg; split <;> decide)]
    exact regs i hi
  refine WP.seq (WP.mono (validateOutgoing_ok allocsp allocwr allocregs) fun a ⟨slots, Oa, Ka⟩ => ?_)
  have asp : a.gpr .esp = P.geometry.frame - 24#32 := (Ka.1 _ (by decide)).trans allocsp
  have aw : (⟨P.geometry.base, usedBytes P.geometry.pLen⟩ : Region) ∈ a.wr := by
    rw [Ka.2.2, allocated_wr]; exact List.mem_cons_of_mem _ R.arena.arenaWrite
  have args : (⟨validateArgsBase P.geometry, 24⟩ : Region) ∈ a.wr := by rw [Ka.2.2]; exact allocwr
  obtain ⟨read, write⟩ := validate_covers aw args
  refine WP.mono (validateCall_ok F asp slots read write) fun b ⟨ax, Ob, Kb⟩ => ?_
  have inner : Keeps [.eax, .ecx, .edx] (allocated 24 s) b := (Ka.mono (by decide)).trans Kb
  have K : Keeps [.eax, .ecx, .edx] s (freed 24 b) := by
    refine ⟨?_, inner.2.1, ?_⟩
    · intro r hr
      by_cases eq : r = .esp
      · subst r
        rw [freed_esp, inner.1 _ (by decide), allocated_esp, BitVec.sub_add_cancel]
      · rw [freed_gpr 24 b eq, inner.1 r hr, allocated_gpr 24 s eq]
    · change b.wr.tail = s.wr
      rw [inner.2.2, allocated_wr]
      rfl
  have first : Frame (validateWrites P.geometry) s.mem a.mem := Oa.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨below P.geometry.frame 60, by simp [validateWrites], below_sub (by decide : 24 ≤ 60) (by omega)⟩)
  have total : Frame (validateWrites P.geometry) s.mem (freed 24 b).mem := first.trans Ob
  have result : validateResult P.geometry a.mem = validateResult P.geometry s.mem := by
    unfold validateResult
    rw [drawFrame_bytes first (validate_packedApart _) (by have := P.geometry.width; have := P.geometry.qWidth; omega)]
  exact ⟨R.frame (R.representation.keep total (validate_frameApart _)) (fun _ _ _ => rfl)
    (total.sub (validate_mutable _)) K (by decide), (freed_gpr 24 b (by decide : Reg.eax ≠ .esp)).trans (ax.trans (by rw [result])), total, K⟩
end VG.Proof.Dsa.X86.Generation
