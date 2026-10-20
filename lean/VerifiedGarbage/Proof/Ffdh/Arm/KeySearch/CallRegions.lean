module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds

/-! The selected attempt can narrow permissions to its buffers and arguments;
its stack writes remain below the controller's saved registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

namespace KeyLive
variable {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}

theorem call_sp (h : KeyLive p original used keys scalars s) : (allocated 32 s).sp = callSp p := by
  change s.sp - 32#32 = callSp p
  rw [h.sp, BitVec.sub_sub]
  rfl

theorem covers_writes (h : KeyLive p original used keys scalars s) {u : State}
    (wr : u.wr = (allocated 32 s).wr) : Covers (callWr p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [wr]
  apply List.mem_cons_of_mem
  rw [h.wr, h.input.write_regions]
  simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp

theorem covers_reads (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    {u : State} (rd : u.rd = (allocated 32 s).rd) (wr : u.wr = (allocated 32 s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (h.covers_writes wr).right
  apply Covers.of_sub
  intro r hr
  simp only [callRd, callRdPlain, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | constant
  · refine ⟨rDomain p, ?_, 0, by rw [BitVec.add_zero], by omega⟩
    rw [rd]
    apply List.mem_append_left
    change rDomain p ∈ s.rd
    rw [h.rd, h.input.read_regions]
    simp
  · refine ⟨rRandom p, ?_, used, h.input.tape_addr room, room⟩
    rw [rd]
    apply List.mem_append_left
    change rRandom p ∈ s.rd
    rw [h.rd, h.input.read_regions]
    simp
  · refine ⟨rArguments p, ?_, 0, by rw [BitVec.add_zero], by change 0 + 28 ≤ 32; decide⟩
    rw [wr]
    apply List.mem_append_right
    change rArguments p ∈ ⟨State.addr (allocated 32 s).sp, 32⟩ :: s.wr
    rw [h.call_sp]
    exact List.mem_cons_self
  · refine ⟨r, ?_, 0, by rw [BitVec.add_zero], by omega⟩
    rw [rd]
    apply List.mem_append_left
    change r ∈ s.rd
    rw [h.rd]
    exact h.input.constants_read constant

theorem argument_frame (_h : KeyLive p original used keys scalars s) {u : State}
    (mem : u.mem = callMem p used s.mem (callSp p)) : Frame (callChanges p) s.mem u.mem := by
  rw [mem]
  exact (callMem_frame _ _ _ _).mono (by simp [callChanges, rArguments])

theorem attempt_frame (h : KeyLive p original used keys scalars s) {u t : State} {depth : Nat}
    (mem : u.mem = callMem p used s.mem (callSp p)) (sp : u.sp = callSp p)
    (frame : Frame (callWr p ++ [FrameStack.belowA u.sp depth]) u.mem t.mem) (limit : depth ≤ 176) :
    Frame (callChanges p) s.mem t.mem := by
  apply (h.argument_frame mem).trans
  apply frame.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, by simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
                 rcases hr with rfl | rfl | rfl <;> simp [callChanges], fun _ hi => hi⟩
  · obtain rfl := List.mem_singleton.mp hr
    refine ⟨rCallStack p, by simp [callChanges], ?_⟩
    rw [sp]
    apply FrameStack.belowA_sub limit
    have fit : 232 ≤ p.sp.toNat := h.input.bounds.stackFits
    change 176 ≤ (p.sp - 56#32).toNat
    rw [FrameStack.sub_toNat' (by omega : 56 ≤ p.sp.toNat)]
    omega


end KeyLive
end VG.Proof.Ffdh.Arm.KeySearch
