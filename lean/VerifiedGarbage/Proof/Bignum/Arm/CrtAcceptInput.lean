module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareLayout
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceLayout
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! # Import the ciphertext and save its exact secret range-check bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

structure CrtAcceptInput (base src : BitVec 32) (len w k : Nat) (bs : List Byte) (s : State) : Prop where
  ready : LayoutFrameReady base len w s
  main : CrtMainState base len w s.mem
  source : SavedOperand base src len k 56 12 bs s
  positive : 0 < k
  fits : k ≤ 8 * w
  stackFits : s.sp.toNat + 52 ≤ 2 ^ 32
  write : InRegions s.wr (off (State.addr s.sp) 48) 4
  separate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr s.sp) 48, 4⟩

theorem crt_acceptInput_ok (s : State) {base src : BitVec 32} {len w k : Nat} {bs : List Byte}
    (h : CrtAcceptInput base src len w k bs s) :
    WP isa CrtFn.acceptInput s fun t => LayoutFrameReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 1 = Spec.Rsa.os2ip bs ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        BitVec.ofNat 32 (decide (Spec.Rsa.os2ip bs < numAt s.mem (State.addr base) w 0)).toNat ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t ∧ CrtMainState base len w t.mem := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [CrtFn.acceptInput, WP.seq_iff]
  refine WP.mono (savedOperandLayout_ok s h.ready h.source (by decide : 1 < 8) h.positive h.fits) ?_
  rintro u ⟨readyU, input, keepsU, frameU, restU⟩
  have modulus := keeps_array_num keepsU fits op0 (by decide : 0 ≠ 1)
  rw [WP.seq_iff]
  refine WP.mono (inputCompareLayout_ok u readyU) ?_
  rintro v ⟨readyV, flag, keepsV, frameV, restV⟩
  have modulusV := (keeps_array_num keepsV fits op0 (by decide : 0 ≠ 3)).trans modulus
  have inputV := (keeps_array_num keepsV fits op1 (by decide : 1 ≠ 3)).trans input
  rw [input, modulus] at flag
  have rest := restU.trans restV
  refine WP.mono (saveAcceptanceLayout_ready v readyV
    (by rw [rest.sp]; exact h.stackFits) (by rw [rest.wr, rest.sp]; exact h.write)
    (by rw [rest.sp]; exact h.separate)) ?_
  rintro t ⟨readyT, saved, eq, frameT, restT, _⟩
  rw [rest.sp] at frameT
  have size := h.main.toCrtLayoutState.size
  have header (d : Nat) (hd : d + 4 ≤ 256) :
      t.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32 :=
    (eq.word (d := d) (bits := 32) (by omega)).trans
      ((keeps_header_readW keepsV size hd).trans (keeps_header_readW keepsU size hd))
  have mainT : CrtMainState base len w t.mem :=
    ⟨⟨readyT.layout, readyT.width⟩, (header 224 (by decide)).trans h.main.p,
      (header 228 (by decide)).trans h.main.q, (header 232 (by decide)).trans h.main.product,
      (header 236 (by decide)).trans h.main.compare, (header 240 (by decide)).trans h.main.modulus⟩
  refine ⟨readyT, (eq.number fits (by decide : 0 < 8)).trans modulusV,
    (eq.number fits (by decide : 1 < 8)).trans inputV, ?_,
    ((frameU.trans frameV).mono (by simp)).trans (frameT.mono (by simp)),
    rest.trans (restT.mono (by decide)), mainT⟩
  rw [saved, flag]
  by_cases valid : Spec.Rsa.os2ip bs < numAt s.mem (State.addr base) w 0 <;> simp [valid]

end VG.Proof.Bignum.Arm
