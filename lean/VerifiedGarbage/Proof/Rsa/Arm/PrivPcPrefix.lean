module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots

import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveResult
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyIncoming
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # Save the CRT status and prepare the precomputation scratch arguments -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_dp op2_imm dpVal)

def pcPrefixMem (g : PrivGeometry) (s : State) : Mem :=
  ((s.mem.writeW (off (State.addr g.stack) oR1) (s.gpr .r0)).writeW
    (off (State.addr g.stack) 0) g.workspace).writeW
    (off (State.addr g.stack) 4) (BitVec.ofNat 32 g.scratchLength)

def pcPrefixWrites (g : PrivGeometry) : List Region :=
  [⟨State.addr g.stack, 8⟩, ⟨off (State.addr g.stack) oR1, 4⟩]

theorem preAddress_ok (r : Reg) (s : State) :
    WP isa (.block (preAddress r)) s fun t =>
      t.gpr r = s.sp + BitVec.ofNat 32 oPre ∧ t.mem = s.mem ∧ Rest [r] s t := by
  unfold preAddress
  refine wp_stackAddr (by decide) fun u a => ?_
  refine wp_dp (op2_imm (by decide)) fun t b => WP.block_nil ?_
  exact ⟨by rw [b.gpr, dpVal, a.gpr, BitVec.add_zero], b.mem.trans a.mem,
    (a.rest (by simp)).trans (b.rest (by simp))⟩

theorem pcPrefix_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block pcPrefix) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      t.gpr .r0 = g.precomputation ∧ t.mem = pcPrefixMem g s ∧
      Frame (pcPrefixWrites g) s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  unfold pcPrefix
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveResult_ok s h slots (by decide : 88 ≤ oR1) (by decide : oR1 + 4 ≤ 96)) ?_
  rintro u ⟨hu, slotsU, ptrU, memU, frameU, restU⟩
  refine WP.mono (copyIncoming_ok u hu slotsU (by decide : 14 < 16) (by decide : 0 + 4 ≤ 56) ptrU) ?_
  rintro v ⟨hv, slotsV, memV, frameV, restV⟩
  refine WP.mono (copyIncoming_ok v hv slotsV (by decide : 15 < 16) (by decide : 4 + 4 ≤ 56)
    ((restV.gpr .r12 (by simp)).trans ptrU)) ?_
  rintro z ⟨hz, slotsZ, memZ, frameZ, restZ⟩
  refine WP.mono (preAddress_ok .r0 z) ?_
  rintro t ⟨ptrT, memT, restT⟩
  have unchanged : Frame (bodyWrites g) z.mem t.mem := by rw [memT]; exact Frame.refl _ _
  refine ⟨hz.after unchanged restT, by simpa only [memT] using slotsZ,
    by rw [ptrT, hz.sp]; rfl, ?_, ?_,
    (restU.mono (by simp)).trans ((restV.mono (by simp)).trans
      ((restZ.mono (by simp)).trans (restT.mono (by simp))))⟩
  · rw [memT, memZ, memV, memU]; rfl
  · rw [memT]
    apply Frame.trans (frameU.mono (by simp [pcPrefixWrites]))
    apply Frame.trans (frameV.sub ?_) (frameZ.sub ?_)
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 8⟩, by simp [pcPrefixWrites], Offset.sub_base _ (by decide : 0 + 4 ≤ 8)⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 8⟩, by simp [pcPrefixWrites], Offset.sub_base _ (by decide : 4 + 4 ≤ 8)⟩

theorem pcPrefixMem_scratch (g : PrivGeometry) (s : State) :
    (pcPrefixMem g s).readW (off (State.addr g.stack) 0) 32 = g.workspace := by
  unfold pcPrefixMem
  rw [outside_read32 (writeW32_outside _ _ (d := 4) _ (by decide)) (d := 0) (by decide) (by decide),
    Mem.readW_writeW_self32]

theorem pcPrefixMem_length (g : PrivGeometry) (s : State) :
    (pcPrefixMem g s).readW (off (State.addr g.stack) 4) 32 = BitVec.ofNat 32 g.scratchLength :=
  Mem.readW_writeW_self32 _ _ _

theorem pcPrefixMem_status (g : PrivGeometry) (s : State) :
    (pcPrefixMem g s).readW (off (State.addr g.stack) oR1) 32 = s.gpr .r0 := by
  unfold pcPrefixMem
  rw [outside_read32 (writeW32_outside _ _ (d := 4) _ (by decide)) (d := oR1) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 0) _ (by decide)) (d := oR1) (by decide) (by decide),
    Mem.readW_writeW_self32]
end VG.Proof.Rsa.Arm
