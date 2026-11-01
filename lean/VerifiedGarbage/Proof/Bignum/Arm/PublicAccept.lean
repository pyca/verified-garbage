module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicArithmetic
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
import VerifiedGarbage.Proof.Bignum.Arm.InputCompare
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # Save the exact secret range-check result while preserving every public argument -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem publicCompare_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicOperand base dst np ep xp len k eLen nb eb xb s) :
    WP isa inputCompare s fun t => PublicOperand base dst np ep xp len k eLen nb eb xb t ∧
      t.gpr .r11 = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)).toNat ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (inputCompare_ok s h.ready) ?_
  rintro t ⟨ready, flag, keeps, frame, rest⟩
  have arithmetic := h.toPublicArithmetic.after_array ready keeps frame rest (by decide) (by decide)
  have fits : arrAt (Spec.Rsa.modulusWords k) 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have input := (keeps_array_num keeps fits op1 (by decide : 1 ≠ 3)).trans h.input
  rw [h.input, h.modulus] at flag
  refine ⟨⟨arithmetic, input⟩, ?_, frame, rest⟩
  by_cases valid : Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb
  · simpa [valid] using flag
  · simpa [valid] using flag

theorem publicSaveAcceptance_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicOperand base dst np ep xp len k eLen nb eb xb s)
    (flag : s.gpr .r11 = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)).toNat) :
    WP isa (.block saveAcceptance) s fun t => PublicAccepted base dst np ep xp len k eLen nb eb xb t ∧
      Frame [⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  have write : InRegions s.wr (off (State.addr s.sp) 48) 4 :=
    ⟨_, h.stack.frameWritable, Offset.contains_base _ (by decide) (by decide)⟩
  have sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr s.sp) 48, 4⟩ :=
    h.stack.separate.symm.sub_right (Offset.sub_base _ (by decide))
  refine WP.mono (saveAcceptance_ready s h.ready (by have := h.stack.nowrap; omega) write sep) ?_
  rintro t ⟨ready, saved, eq, frame, rest, mem⟩
  have fits : arrAt (Spec.Rsa.modulusWords k) 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have arithmetic : PublicArithmetic base dst np ep xp len k eLen nb eb xb t :=
    ⟨h.buffers.after_acceptance frame rest, h.stack.after_acceptance mem rest, ready,
      (eq.number fits (by decide : 0 < 8)).trans h.modulus, h.modulusLength, h.odd,
      (eq.number fits (by decide : 4 < 8)).trans h.r2⟩
  exact ⟨⟨⟨arithmetic, (eq.number fits (by decide : 1 < 8)).trans h.input⟩, saved.trans flag⟩, frame, rest⟩

theorem publicAccept_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicOperand base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.acceptInput s fun t => PublicAccepted base dst np ep xp len k eLen nb eb xb t ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PublicFn.acceptInput, WP.seq_iff]
  refine WP.mono (publicCompare_ok s h) ?_
  rintro u ⟨operand, flag, frameU, restU⟩
  refine WP.mono (publicSaveAcceptance_ok u operand flag) ?_
  rintro t ⟨accepted, frameT, restT⟩
  rw [restU.sp] at frameT
  exact ⟨accepted, (frameU.mono (by simp)).trans (frameT.mono (by simp)),
    restU.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
