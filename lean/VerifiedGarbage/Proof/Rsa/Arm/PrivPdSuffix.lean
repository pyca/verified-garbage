module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots

import VerifiedGarbage.Proof.Rsa.Arm.PrivPcPrefix
import VerifiedGarbage.Proof.Rsa.Arm.PrivPreWords
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # The four register arguments of the public re-exponentiation call -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pdHead_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block [.ldrSp .r0 oOut, .ldrSp .r1 oK]) s fun t =>
      t.gpr .r0 = g.output ∧ t.gpr .r1 = BitVec.ofNat 32 g.length ∧
      t.mem = s.mem ∧ Rest [.r0, .r1] s t := by
  refine wp_loadStack (a := off (State.addr g.stack) oOut) (by decide)
    (by rw [h.sp]; exact addr_add (by have := h.valid.stackHigh; simp only [oOut, frameBytes] at *; omega))
    (h.inner.read (by decide)) fun u a => ?_
  refine wp_loadStack (a := off (State.addr g.stack) oK) (by decide)
    (by rw [a.sp, h.sp]; exact addr_add (by have := h.valid.stackHigh; simp only [oK, frameBytes] at *; omega))
    (by rw [a.rd, a.wr]; exact h.inner.read (by decide)) fun t b => WP.block_nil ?_
  exact ⟨by rw [b.other .r0 (by decide), a.gpr]; exact slots 0 (by decide),
    by rw [b.gpr, a.mem]; exact slots 2 (by decide), b.mem.trans a.mem,
    (a.rest (by simp)).trans (b.rest (by simp))⟩

theorem pdSuffix_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block pdSuffix) s fun t =>
      t.gpr .r0 = g.output ∧ t.gpr .r1 = BitVec.ofNat 32 g.length ∧
      t.gpr .r2 = g.precomputation ∧ t.gpr .r3 = BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length) ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3] s t := by
  unfold pdSuffix
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pdHead_ok s h slots) ?_
  rintro u ⟨outU, lenU, memU, restU⟩
  refine WP.mono (preAddress_ok .r2 u) ?_
  rintro v ⟨preV, memV, restV⟩
  have memSV : v.mem = s.mem := memV.trans memU
  have restSV : Rest [.r0, .r1, .r2] s v := (restU.mono (by simp)).trans (restV.mono (by simp))
  have hv : PrivContext g bs v := h.after (by rw [memSV]; exact Frame.refl _ _) restSV
  refine WP.mono (preWords_ok .r3 v hv (by rw [memSV]; exact slots)) ?_
  rintro t ⟨lenT, memT, restT⟩
  refine ⟨(restT.gpr .r0 (by simp)).trans ((restV.gpr .r0 (by simp)).trans outU),
    (restT.gpr .r1 (by simp)).trans ((restV.gpr .r1 (by simp)).trans lenU), ?_, lenT, memT.trans memSV,
    (restSV.mono (by simp)).trans (restT.mono (by simp))⟩
  rw [restT.gpr .r2 (by simp), preV, restU.sp, h.sp]; rfl
end VG.Proof.Rsa.Arm
