module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivPcPrefix
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPreWords
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Register and stack arguments for the public precomputation call -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pcSuffix_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block pcSuffix) s fun t =>
      t.gpr .r2 = g.sources 0 ∧ t.gpr .r3 = BitVec.ofNat 32 g.length ∧
      t.mem = s.mem ∧ Rest [.r2, .r3] s t := by
  unfold pcSuffix
  refine wp_loadStack (a := off (State.addr g.stack) oN) (by decide)
    (by rw [h.sp]; exact addr_add (by have := h.valid.stackHigh; simp only [oN, frameBytes] at *; omega))
    (h.inner.read (by decide)) fun u a => ?_
  refine wp_loadStack (a := off (State.addr g.stack) oK) (by decide)
    (by rw [a.sp, h.sp]; exact addr_add (by have := h.valid.stackHigh; simp only [oK, frameBytes] at *; omega))
    (by rw [a.rd, a.wr]; exact h.inner.read (by decide)) fun t b => WP.block_nil ?_
  exact ⟨by rw [b.other .r2 (by decide), a.gpr]; exact slots 1 (by decide),
    by rw [b.gpr, a.mem]; exact slots 2 (by decide), b.mem.trans a.mem,
    (a.rest (by simp)).trans (b.rest (by simp))⟩

structure PcArgs (g : PrivGeometry) (s : State) : Prop where
  output : s.gpr .r0 = g.precomputation
  outputLength : s.gpr .r1 = BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length)
  modulus : s.gpr .r2 = g.sources 0
  length : s.gpr .r3 = BitVec.ofNat 32 g.length
  workspace : s.mem.readW (off (State.addr g.stack) 0) 32 = g.workspace
  workspaceLength : s.mem.readW (off (State.addr g.stack) 4) 32 = BitVec.ofNat 32 g.scratchLength

theorem pcArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block pcArgs) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧ PcArgs g t ∧
      t.mem.readW (off (State.addr g.stack) oR1) 32 = s.gpr .r0 ∧
      Frame (pcPrefixWrites g) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r12] s t := by
  unfold pcArgs
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pcPrefix_ok s h slots) ?_
  rintro u ⟨hu, slotsU, ptrU, memU, frameU, restU⟩
  refine WP.mono (preWords_ok .r1 u hu slotsU) ?_
  rintro v ⟨countV, memV, restV⟩
  have frameUV : Frame (bodyWrites g) u.mem v.mem := by rw [memV]; exact Frame.refl _ _
  have hv := hu.after frameUV restV
  have slotsV : PrivSlots g v.mem := by rw [memV]; exact slotsU
  refine WP.mono (pcSuffix_ok v hv slotsV) ?_
  rintro t ⟨modulusT, countT, memT, restT⟩
  have frameVT : Frame (bodyWrites g) v.mem t.mem := by rw [memT]; exact Frame.refl _ _
  refine ⟨hv.after frameVT restT, by rw [memT]; exact slotsV,
    ⟨(restT.gpr .r0 (by simp)).trans ((restV.gpr .r0 (by simp)).trans ptrU),
      (restT.gpr .r1 (by simp)).trans countV, modulusT, countT, ?_, ?_⟩, ?_, ?_,
    (restU.mono (by simp)).trans ((restV.mono (by simp)).trans (restT.mono (by simp)))⟩
  · rw [memT, memV, memU]; exact pcPrefixMem_scratch g s
  · rw [memT, memV, memU]; exact pcPrefixMem_length g s
  · rw [memT, memV, memU]; exact pcPrefixMem_status g s
  · rw [memT, memV]; exact frameU
end VG.Proof.Rsa.Arm
