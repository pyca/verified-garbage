module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots

import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveIncoming
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyArgs
import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveRegs
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Block

/-! # Prepare all register and stack arguments of the private CRT call -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem saveSlots_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivContext g bs s)
    (output : s.gpr .r0 = g.output) (modulus : s.gpr .r2 = g.sources 0) (count : s.gpr .r3 = BitVec.ofNat 32 g.length) :
    WP isa (.block saveSlots) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      t.gpr .r12 = g.stack ∧ Frame [g.innerRegion] s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  unfold saveSlots
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok s h output modulus count) ?_
  rintro u ⟨hu, slots, ptr, frameU, restU⟩
  refine WP.mono (saveIncoming_prefix_ok 3 (by decide) u hu slots ptr) ?_
  rintro t ⟨ht, slotsT, frameT, restT⟩
  exact ⟨ht, slotsT, (restT.gpr .r12 (by simp)).trans ptr, frameU.trans frameT,
    (restU.mono (by simp)).trans (restT.mono (by simp))⟩

structure CrtArgs (g : PrivGeometry) (s : State) : Prop where
  output : s.gpr .r0 = g.temporary
  outputLength : s.gpr .r1 = BitVec.ofNat 32 g.length
  modulus : s.gpr .r2 = g.sources 0
  length : s.gpr .r3 = BitVec.ofNat 32 g.length
  arguments : ∀ j < 14, s.mem.readW (off (State.addr g.stack) (4 * j)) 32 = g.argument (j + 2)

theorem crtRegs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivContext g bs s)
    (modulus : s.gpr .r2 = g.sources 0) (count : s.gpr .r3 = BitVec.ofNat 32 g.length)
    (args : ∀ j < 14, s.mem.readW (off (State.addr g.stack) (4 * j)) 32 = g.argument (j + 2)) :
    WP isa (.block crtRegs) s fun t => CrtArgs g t ∧ t.mem = s.mem ∧ Rest [.r0, .r1] s t := by
  unfold crtRegs
  refine wp_stackAddr (by decide) fun u a => ?_
  refine wp_mov (op2_reg _ _) fun t b => WP.block_nil ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, b.mem.trans a.mem, (a.rest (by simp)).trans (b.rest (by simp))⟩
  · rw [b.other .r0 (by decide), a.gpr, h.sp]; rfl
  · rw [b.gpr, a.other .r3 (by decide), count]
  · rw [b.other .r2 (by decide), a.other .r2 (by decide), modulus]
  · rw [b.other .r3 (by decide), a.other .r3 (by decide), count]
  · simpa only [b.mem, a.mem] using args

theorem crtArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivContext g bs s)
    (output : s.gpr .r0 = g.output) (modulus : s.gpr .r2 = g.sources 0) (count : s.gpr .r3 = BitVec.ofNat 32 g.length) :
    WP isa (.block crtArgs) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧ CrtArgs g t ∧
      Frame [g.innerRegion] s.mem t.mem ∧ Rest [.r0, .r1, .r12] s t := by
  unfold crtArgs
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveSlots_ok s h output modulus count) ?_
  rintro u ⟨hu, slotsU, ptr, frameU, restU⟩
  refine WP.mono (copyArgs_ok u hu slotsU ptr) ?_
  rintro v ⟨hv, slotsV, args, frameV, restV⟩
  have restUV : Rest [.r0, .r12] s v := restU.trans (restV.mono (by simp))
  refine WP.mono (crtRegs_ok v hv ((restUV.gpr .r2 (by simp)).trans modulus)
    ((restUV.gpr .r3 (by simp)).trans count) args) ?_
  rintro t ⟨argsT, mem, restT⟩
  have frameVT : Frame (bodyWrites g) v.mem t.mem := by rw [mem]; exact Frame.refl _ _
  refine ⟨hv.after frameVT restT, by simpa only [mem] using slotsV, argsT, ?_,
    (restUV.mono (by simp)).trans (restT.mono (by simp))⟩
  rw [mem]
  exact frameU.trans (frameV.sub (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨g.innerRegion, by simp, Region.sub_prefix (by decide : 56 ≤ frameBytes)⟩))
end VG.Proof.Rsa.Arm
