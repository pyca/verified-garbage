module

public import VerifiedGarbage.Proof.Bignum.Arm.PcInput
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryMemory
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.CallLay

/-! # Establish all precomputation-body assumptions from AAPCS arguments -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pc_entry_ready (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcFnInput base dst src len k s) :
    WP isa (.block PcFn.entry) (pcPushed s) fun t =>
      PcBodyInput base dst src len k t ∧
      Frame [FrameStack.belowA s.sp 56] s.mem t.mem ∧
      Spill.Saved t.mem (State.addr t.sp) s.gpr pcCalleeSaved ∧ Rest roundClobbers (pcPushed s) t := by
  have pushFrame := FrameStack.pushed_frameA
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) h.stackFit
  have spNat : (pcPushed s).sp.toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' h.stackFit
  have argAddr : off (State.addr (pcPushed s).sp) 56 = State.addr s.sp := by
    change State.addr (pcPushed s).sp + BitVec.ofNat 64 56 = State.addr s.sp
    rw [← addr_add (a := (pcPushed s).sp) (k := 56) (by rw [spNat]; have := s.sp.isLt; omega)]
    change State.addr (s.sp - BitVec.ofNat 32 56 + BitVec.ofNat 32 56) = _
    rw [BitVec.sub_add_cancel]
  have stackWrite : (⟨State.addr (pcPushed s).sp, 56⟩ : Region) ∈ (pcPushed s).wr := List.mem_cons_self
  have argRead : InRegions ((pcPushed s).rd ++ (pcPushed s).wr) (off (State.addr (pcPushed s).sp) 56) 4 := by
    rw [argAddr]
    apply InRegions_append_cons.mpr
    right
    change InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) h.argRead (by decide) (by decide)
  have arg : (pcPushed s).mem.readW (off (State.addr (pcPushed s).sp) 56) 32 = base := by
    rw [argAddr, pushFrame.readW (r := ⟨State.addr s.sp, 8⟩) (by simp [Region.Contains])
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackArgs.symm) (by decide)]
    exact h.workspaceArg
  refine WP.mono (pcEntry_ok (pcPushed s) (by rw [spNat]; have := h.argFit; omega) stackWrite argRead arg) ?_
  rintro t ⟨ptr, source, count, mem, rest⟩
  obtain ⟨savedBase, savedOutput, outside, frameEntry⟩ := pcEntry_memory mem
  have savedAll := pc_push_saved s h.stackFit
  have frameEntryFull : Frame [FrameStack.belowA s.sp 56] (pcPushed s).mem t.mem :=
    frameEntry.sub (by intro r hr; simp only [List.mem_singleton] at hr; subst r
                       exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
  have savedCallee := pcEntry_callee_saved (pc_push_callee_saved s h.stackFit) mem
  refine ⟨?_, pushFrame.trans frameEntryFull, ?_, rest.mono (by decide)⟩
  · refine ⟨⟨⟨h.workspace.nowrap, ?_⟩, h.minLength, h.maxLength, h.space, h.sourceFits, ?_,
      h.sourceSeparate, h.outputFits, ?_, h.outputSeparate⟩, ?_, ptr,
      source.trans h.source, count.trans h.count⟩
    · rw [rest.wr]; exact List.mem_cons_of_mem _ h.workspace.writable
    · rw [rest.rd, rest.wr]; exact InRegions_append_cons.mpr (Or.inr h.readable)
    · rw [rest.wr]
      obtain ⟨r, hr, hc⟩ := h.writable
      exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [rest.sp, spNat]; have := s.sp.isLt; have := h.stackFit; omega
      · rw [rest.rd, rest.wr, rest.sp]
        exact ⟨_, List.mem_append_right _ stackWrite, by simp [Region.Contains]⟩
      · rw [rest.sp]
        exact h.stackWorkspace.sub_left (Region.sub_prefix (by decide))
      · rw [rest.sp]; exact savedBase
      · rw [rest.sp]; exact savedOutput.trans h.output
      · rw [rest.sp, outside_read32 outside (d := 8) (by decide) (by decide)]
        exact (savedAll (.r2, 8) (by decide)).trans h.source
      · rw [rest.sp, outside_read32 outside (d := 12) (by decide) (by decide)]
        exact (savedAll (.r3, 12) (by decide)).trans h.count
  · rw [rest.sp]; exact savedCallee

end VG.Proof.Bignum.Arm
