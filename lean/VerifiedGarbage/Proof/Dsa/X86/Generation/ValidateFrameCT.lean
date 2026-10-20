module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.AllocationCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateOutgoing
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateResources
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateCallCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PackCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.AllocationCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateOutgoing
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateResources

/-! # A fixed outgoing frame isolates public domain-check arguments -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

structure ValidateOutgoingAt (G : GenerationGeometry) (bytes : List Byte) (s : State) : Prop where
  sp : s.gpr .esp = G.frame - 24#32
  args : (⟨validateArgsBase G, 24⟩ : Region) ∈ s.wr
  arena : (⟨G.base, usedBytes G.pLen⟩ : Region) ∈ s.wr
  regs : ValidateRegs G s
  bytes : Spec.Rsa.bytesAt s.mem (off G.base packed) (2 * G.pLen + G.qLen) = bytes

def ValidateFrameAt (P : SearchContextPlan) (bytes : List Byte) (s : State) : Prop :=
  SearchContextAt P s ∧ ValidateRegs P.geometry s ∧
    Spec.Rsa.bytesAt s.mem (off P.geometry.base packed) (2 * P.geometry.pLen + P.geometry.qLen) = bytes

theorem validateOutgoing_ct (G : GenerationGeometry) (bytes : List Byte) : RelCT isa
    (Two fun (_ : Unit) => ValidateOutgoingAt G bytes) (.block validateOutgoing)
    (Two fun (_ : Unit) => ValidateCallAt G bytes) := by
  refine two_piece [.esp] ?_ (by taint_decide) ?_
  · intro _ s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.sp.trans ht.sp.symm
  · intro _ s R
    refine WP.mono (validateOutgoing_ok R.sp R.args R.regs) fun t ⟨slots, O, K⟩ => ?_
    obtain ⟨read, write⟩ := validate_covers (by rw [K.2.2]; exact R.arena) (by rw [K.2.2]; exact R.args)
    refine ⟨(K.1 _ (by simp)).trans R.sp, slots, read, write, ?_⟩
    rw [drawFrame_bytes O (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact G.stack_slice_apart (by decide : 24 ≤ 24) (by decide : 24 ≤ 128) (validate_packed_room G))
      (by have := G.width; have := G.qWidth; omega), R.bytes]

theorem validateFrame_ct (F : KeyRandom.CheckCall.CheckFn) (P : SearchContextPlan) (bytes : List Byte) :
    RelCT isa (Two fun (_ : Unit) => ValidateFrameAt P bytes)
      (.frame (.alloc 24) (.seq (.block validateOutgoing) (.call F.name F.code)) (.free 24)) (fun _ _ => True) := by
  refine allocation_ct (Ψ := fun (_ : Unit) => ValidateOutgoingAt P.geometry bytes) (by decide) ?_ ?_
    (RelCT.seq (validateOutgoing_ct P.geometry bytes) (validateCall_ct F P.geometry bytes))
  · rintro _ s ⟨⟨W, R⟩, _, _⟩
    rw [R.arena.frameReg]
    have := P.geometry.stackSize
    omega
  · rintro _ s ⟨⟨W, R⟩, regs, value⟩
    refine ⟨by rw [allocated_esp, R.arena.frameReg], ?_, ?_, ?_, value⟩
    · rw [allocated_wr, R.arena.frameReg]
      exact List.mem_cons_self
    · rw [allocated_wr]
      exact List.mem_cons_of_mem _ R.arena.arenaWrite
    · intro i hi
      rw [allocated_gpr 24 s (show validateReg i ≠ .esp from by unfold validateReg; split <;> decide)]
      exact regs i hi
end VG.Proof.Dsa.X86.Generation
