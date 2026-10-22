module

public import VerifiedGarbage.Proof.MillerRabin.X86.BackupTiming
import VerifiedGarbage.Proof.Framework.Offset

/-! # The cdecl entry reads only public arguments at public stack addresses -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

namespace RoundABI

theorem allocated_low {s : State} (A : RoundABI s) : 1132 ≤ (s.gpr .esp).toNat := by
  have := A.stackLow
  change 1172 ≤ (s.gpr .esp).toNat at this
  omega

theorem arg_byte_alloc {s : State} (A : RoundABI s) (k : Nat) :
    VG.X86.Taint.argByte (allocFrame 1132 s) (1132 + k) = VG.X86.Taint.argByte s k := by
  simp only [VG.X86.Taint.argByte, allocFrame_esp]
  rw [VG.X86.Taint.sub_setWidth A.allocated_low, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem entry_wf {s : State} (A : RoundABI s) :
    VG.X86.Taint.Wf entryTaint (allocFrame 1132 s) := by
  have bound := A.stackBound
  have esp := (s.gpr .esp).isLt
  have eN := A.allocated_sp
  simp only [VG.Impl.MillerRabin.X86.frameBytes] at eN
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨?_, fun r hr => ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, ?_, fun p hp => ?_, fun h => absurd h (by decide)⟩
  · change _ + 1132 + 12 ≤ _
    rw [eN]
    have := A.allocated_low
    omega
  · rw [show VG.X86.Taint.depth entryTaint.stk = 1132 + 0 from rfl,
      A.arg_byte_alloc, VG.X86.Taint.argByte, BitVec.add_zero]
    rw [allocFrame_wr, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [VG.X86.Taint.sub_setWidth A.allocated_low]
      exact Offset.base_disjoint_below _ (by decide)
    · rw [A.wr, List.mem_singleton] at hr
      subst r
      apply VG.X86.Taint.frame_disjoint (n := 8) (by omega) A.retScratch
      exact A.argScratch
  · change _ + 1132 < _
    rw [eN]
    have := A.allocated_low
    omega
  · simp only [entryTaint, VG.X86.Taint.frameList, List.mem_singleton] at hp
    subst p
    simp only [allocFrame_wr, allocFrame_esp, List.getElem?_cons_zero, addr, BitVec.add_zero]

theorem entry_agree {s t : State} (A : RoundABI s) (B : RoundABI t)
    (sp : s.gpr .esp = t.gpr .esp) (args : ∀ i, i < 2 → arg s i = arg t i) :
    VG.X86.Taint.Agree entryTaint (allocFrame 1132 s) (allocFrame 1132 t) := by
  refine ⟨⟨?_, fun h => nomatch h⟩, fun h => absurd rfl h, A.entry_wf, B.entry_wf,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty,
    fun _ => by simp only [allocFrame_esp, sp], ?_⟩
  · intro r hr
    simp only [entryTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r
    simp only [allocFrame_esp, sp]
  · intro k h4 hk
    change k < 12 at hk
    rw [show VG.X86.Taint.depth entryTaint.stk = 1132 from rfl,
      A.arg_byte_alloc, B.arg_byte_alloc, allocFrame_mem, allocFrame_mem,
      VG.X86.Taint.argByte_eq A.stackBound h4 hk, VG.X86.Taint.argByte_eq B.stackBound h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args _ (by omega))

end RoundABI

theorem PieceInput.of_entry {s u : State} (A : RoundABI s) (entry : EntryReady s u) :
    PieceInput (wsOf s) (bytesOf s) (Spec.Rsa.Mont.wOf s.mem (wsOf s))
      ((allocFrame 1132 s).gpr .esp) (arg s 1) u := by
  obtain ⟨layout, prepared, width⟩ := workspace_congr (frame_workspace_same A entry.frame) A.layout A.prepared
  have facts := round_facts_of (bytes := bytesOf s) rfl width layout prepared entry.length
  have sp := entry.keeps.1 .esp (by decide)
  change u.gpr .esp = (allocFrame 1132 s).gpr .esp at sp
  refine ⟨entry.context, entry.room, ?_, sp, capacity_min facts.lower facts.fit, facts.width, ?_⟩
  · rw [entry.keeps.2.2, allocFrame_wr, A.wr]
    rfl
  · rw [← sp]
    exact entry.length

end VG.Proof.MillerRabin.X86
