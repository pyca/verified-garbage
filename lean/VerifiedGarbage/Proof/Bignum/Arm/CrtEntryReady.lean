module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtEntry
public import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryBuffers
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Establish the private RSA body and saved-register invariants from native arguments -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_entry_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtFnInput g bs s) :
    WP isa (.block CrtFn.entry) (pcPushed s) fun t => CrtScopedInput g bs t ∧
      Frame [FrameStack.belowA s.sp 56] s.mem t.mem ∧
      Spill.Saved t.mem (State.addr t.sp) s.gpr pcCalleeSaved ∧ Rest roundClobbers (pcPushed s) t := by
  have pushFrame := FrameStack.pushed_frameA
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) h.stackFit
  have spNat : (pcPushed s).sp.toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' h.stackFit
  obtain ⟨argRead, argEq⟩ := crt_push_arguments h
  have argOffset (d : Nat) : VG.Proof.Mont.off (State.addr (pcPushed s).sp) (56 + d) = VG.Proof.Mont.off (State.addr s.sp) d :=
    public_push_argOffset h.stackFit d
  have readBase := CallLay.inRegions_sub (off := 48) argRead (l := 4) (by decide) (by decide)
  rw [show off (State.addr (pcPushed s).sp) 56 + BitVec.ofNat 64 48 = off (State.addr (pcPushed s).sp) 104
    from Offset.add_add _ 56 48] at readBase
  have baseArg : (pcPushed s).mem.readW (off (State.addr (pcPushed s).sp) 104) 32 = g.base := by
    rw [public_push_argOffset h.stackFit 48, argEq.word (d := 48) (bits := 32) (by decide)]
    exact h.workspaceArg
  refine WP.mono (crt_entry_ok (pcPushed s) (by rw [spNat]; have := h.argFit; omega)
    (List.mem_cons_self) readBase baseArg) ?_
  rintro t ⟨ptr, source, count, mem, rest⟩
  obtain ⟨savedBase, savedOutput, outside, frameEntry⟩ := pcEntry_memory mem
  have frameEntryFull : Frame [FrameStack.belowA s.sp 56] (pcPushed s).mem t.mem :=
    frameEntry.sub (by intro r hr; simp only [List.mem_singleton] at hr; subst r
                       exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
  have frame := pushFrame.trans frameEntryFull
  have savedAll := pc_push_saved s h.stackFit
  have savedCallee := pcEntry_callee_saved (pc_push_callee_saved s h.stackFit) mem
  have stack : CrtCallStack g (crtExpanded t g.base g.words) := by
    refine ⟨?_, crtExpanded_read ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change t.sp.toNat + 112 ≤ _
      rw [rest.sp, spNat]; have := h.argFit; omega
    · change InRegions (t.rd ++ t.wr) (VG.Proof.Mont.off (State.addr t.sp) 56) 56
      rw [rest.rd, rest.wr, rest.sp]; exact argRead
    · change (⟨State.addr t.sp, 56⟩ : Region) ∈ _ ++ t.wr
      rw [rest.wr, rest.sp]
      exact List.mem_append_right _ List.mem_cons_self
    · change Region.Disjoint ⟨State.addr t.sp, 112⟩ _
      rw [rest.sp]; exact crt_push_separate h
    · change t.mem.readW (off (State.addr t.sp) 4) 32 = _
      rw [rest.sp]; exact savedOutput.trans h.output
    · change t.mem.readW (off (State.addr t.sp) 12) 32 = _
      rw [rest.sp, outside_read32 outside (d := 12) (by decide) (by decide)]
      exact (savedAll (.r3, 12) (by simp [pcAllSaved])).trans h.count
    · intro i
      change t.mem.readW (off (State.addr t.sp) (56 + 8 * i.val)) 32 = _
      rw [rest.sp, outside_read32 outside (d := 56 + 8 * i.val) (by omega) (by have := i.isLt; omega),
        argOffset (8 * i.val), argEq.word (d := 8 * i.val) (bits := 32) (by have := i.isLt; omega)]
      exact h.pointer i
    · intro i
      change t.mem.readW (off (State.addr t.sp) (60 + 8 * i.val)) 32 = _
      rw [rest.sp, outside_read32 outside (d := 60 + 8 * i.val) (by omega) (by have := i.isLt; omega),
        show 60 + 8 * i.val = 56 + (4 + 8 * i.val) by omega,
        argOffset (4 + 8 * i.val), argEq.word (d := 4 + 8 * i.val) (bits := 32) (by have := i.isLt; omega)]
      exact h.length i
  refine ⟨⟨⟨h.workspace.nowrap, by rw [rest.wr]; exact List.mem_cons_of_mem _ h.workspace.writable⟩,
    ⟨crt_entry_buffers h frame rest, stack, ptr, source.trans h.modulus, count.trans h.count, ?_, ?_⟩⟩,
    frame, ?_, rest.mono (by simp [roundClobbers])⟩
  · change t.mem.readW (State.addr t.sp) 32 = _
    rw [rest.sp]; exact savedBase
  · change t.mem.readW (off (State.addr t.sp) 8) 32 = _
    rw [rest.sp, outside_read32 outside (d := 8) (by decide) (by decide)]
    exact (savedAll (.r2, 8) (by simp [pcAllSaved])).trans h.modulus
  · rw [rest.sp]; exact savedCallee

end VG.Proof.Bignum.Arm
