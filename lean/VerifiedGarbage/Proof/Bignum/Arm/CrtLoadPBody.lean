module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareLayout
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceLayout
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # Import p and qInv and accumulate the exact qInv < p check -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

structure CrtLoadPInput (base pp qp : BitVec 32) (len w k : Nat) (pb qb : List Byte) (s : State) : Prop where
  ready : LayoutFrameReady base len w s
  prime : SavedOperand base pp len k 64 68 pb s
  inverse : SavedOperand base qp len k 96 100 qb s
  positive : 0 < k
  fits : k ≤ 8 * w
  write : InRegions s.wr (off (State.addr s.sp) 48) 4

theorem crt_loadPBody_ok (s : State) {base pp qp : BitVec 32} {len w k : Nat} {pb qb : List Byte}
    (h : CrtLoadPInput base pp qp len w k pb qb s) :
    WP isa CrtFn.loadPBody s fun t => LayoutFrameReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = Spec.Rsa.os2ip pb ∧
      numAt t.mem (State.addr base) w 1 = Spec.Rsa.os2ip qb ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        (if Spec.Rsa.os2ip qb < Spec.Rsa.os2ip pb then 1 else 0) &&& s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [CrtFn.loadPBody, WP.seq_iff]
  refine WP.mono (savedOperandLayout_ok s h.ready h.prime (by decide : 0 < 8) h.positive h.fits) ?_
  rintro u ⟨readyU, prime, _, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (savedOperandLayout_ok u readyU (h.inverse.after_workspace frameU restU)
    (by decide : 1 < 8) h.positive h.fits) ?_
  rintro v ⟨readyV, inverse, keepsV, frameV, restV⟩
  have primeV := (keeps_array_num keepsV fits op0 (by decide : 0 ≠ 1)).trans prime
  rw [WP.seq_iff]
  refine WP.mono (inputCompareLayout_ok v readyV) ?_
  rintro z ⟨readyZ, flag, keepsZ, frameZ, restZ⟩
  have primeZ := (keeps_array_num keepsZ fits op0 (by decide : 0 ≠ 3)).trans primeV
  have inverseZ := (keeps_array_num keepsZ fits op1 (by decide : 1 ≠ 3)).trans inverse
  rw [inverse, primeV] at flag
  have rest := (restU.trans restV).trans restZ
  have frame := (frameU.trans frameV).trans frameZ
  have stack := WorkspaceEq.of_frame (by decide : 112 < 2 ^ 64) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.prime.stackSeparate)
  have old : z.mem.readW (off (State.addr z.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [rest.sp]; exact stack.word (d := 48) (bits := 32) (by decide)
  refine WP.mono (mergeAcceptanceLayout_ready z readyZ
    (by rw [rest.sp]; have := h.prime.nowrap; omega) (by rw [rest.wr, rest.sp]; exact h.write)
    (by rw [rest.sp]; exact h.prime.stackSeparate.symm.sub_right (Offset.sub_base _ (by decide)))) ?_
  rintro t ⟨readyT, saved, eq, frameT, restT, _⟩
  rw [rest.sp] at frameT
  exact ⟨readyT, (eq.number fits (by decide : 0 < 8)).trans primeZ,
    (eq.number fits (by decide : 1 < 8)).trans inverseZ, by rw [saved, flag, old],
    (frame.mono (by simp)).trans (frameT.mono (by simp)),
    rest.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
