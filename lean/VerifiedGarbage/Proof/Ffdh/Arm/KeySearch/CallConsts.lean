module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPre
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantContract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract

/-! The nested attempt receives the policy's preserved public constant tables. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}
open VG VG.Arm VG.Proof.Mont

 theorem strip_call {p : KeyPublic sampling} {used : Nat} {u : State} :
    stripConsts (KeyConstants.consts sampling) (callState p used u) = plainCallState p used u := by
  cases sampling <;> rfl

 theorem call_consts {p : KeyPublic sampling} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s)
    (mem : u.mem = callMem p used s.mem (callSp p)) (sp : u.sp = callSp p) (syms : u.syms = s.syms) :
    ConstsOk (KeyConstants.consts sampling) 176 (callState p used u) := by
  have pointer : KeyConstants.tablePtr sampling (callState p used u) = p.tablePtr :=
    (KeyConstants.tablePtr_of_syms (sampling := sampling) syms).trans h.tablePtr
  have regions : constRegs (KeyConstants.consts sampling) (callState p used u) =
      KeyConstants.regions sampling p.tablePtr := by
    rw [KeyConstants.regions_eq, pointer]
  have frame : Frame [rArguments p] s.mem u.mem := by rw [mem]; exact callMem_frame _ _ _ _
  have held := KeyConstants.held_after_frame h.held frame (by
    intro table member r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.input.constants_stack table member).sub_right (arguments_sub h.input.bounds.stackFits))
  refine ⟨?_, ?_, ?_⟩
  · rw [regions]
    cases sampling <;> rfl
  · intro c member i hi
    have word := held c member i hi
    cases sampling with
    | full => exact False.elim (List.not_mem_nil member)
    | vetted =>
      simp only [KeyConstants.consts, VG.Impl.Ffdh.Arm.VettedGroups.tableConsts, List.mem_singleton] at member
      subst c
      change u.mem.readW (State.addr (u.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym) + BitVec.ofNat 64 (8 * i)) 64 = _
      change u.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym = p.tablePtr at pointer
      rw [pointer]
      exact word
  · intro table member
    rw [regions] at member
    have initial : ConstsOk (KeyConstants.consts sampling) stackUse original := h.input.2.2
    have originalMember : table ∈ constRegs (KeyConstants.consts sampling) original := by
      rw [h.input.constant_regions]; exact member
    have facts := initial.2.2 table originalMember
    refine ⟨facts.1, ?_, ?_⟩
    · intro r hr
      have changes : r ∈ callChanges p := by
        change r ∈ callWr p at hr
        simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [callChanges]
      exact h.input.call_read (h.input.constants_read member) r changes
    · intro r hr
      change r ∈ stackBelow (State.addr u.sp) 176 at hr
      simp only [stackBelow, List.mem_singleton] at hr
      subst r
      rw [sp]
      have fit : 176 ≤ (callSp p).toNat := by
        have enough : 232 ≤ p.sp.toNat := h.input.bounds.stackFits
        rw [callSp, FrameStack.sub_toNat' (by omega : 56 ≤ p.sp.toNat)]
        omega
      rw [← FrameStack.addr_sub' fit]
      exact (h.input.constants_stack table member).sub_right (callStack_sub h.input.bounds.stackFits)

 theorem call_pre {p : KeyPublic sampling} {used keys scalars : Nat} {original s u : State}
    (live : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (args : ArgumentContext p used keys scalars u) (sp : u.sp = callSp p)
    (mem : u.mem = callMem p used s.mem (callSp p)) (syms : u.syms = s.syms) :
    (GenerationPolicy.attemptContract sampling (KeyConstants.abi sampling) 176).pre (callState p used u) := by
  apply selected_attempt_pre.mpr
  rw [strip_call]
  exact ⟨call_pre_plain (live.input.callFacts room) args sp mem, call_consts live mem sp syms⟩

end VG.Proof.Ffdh.Arm.KeySearch
