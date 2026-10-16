module

public import VerifiedGarbage.Proof.Bignum.Arm.SelectPowerArgs
public import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Branchless selection of the squared or multiplied private power -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem selectPower_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) (bit : (s.gpr .r11).toNat ≤ 1) :
    WP isa selectPower s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = (if (s.gpr .r11).toNat = 0 then
        numAt s.mem (State.addr base) w 6 else numAt s.mem (State.addr base) w 1) ∧
      Keeps (State.addr base) len w 6 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
  have f1 := Nat.le_trans (array_end_le (w := w) (by decide : 1 < 8)) fits
  have f6 := Nat.le_trans (array_end_le (w := w) (by decide : 6 < 8)) fits
  have sep := array_end_le (w := w) (by decide : 1 < 6)
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  rw [selectPower, WP.seq_iff]
  refine WP.mono (selectPowerArgs_ok s h.workspace size header h.ptr) ?_
  rintro u ⟨p0, p10, p12, count, memU, restU⟩
  have ctx : SelectCtx u base (8 * len) (arrAt w 6) (arrAt w 6) (arrAt w 1) (2 * w) :=
    ⟨h.workspace.nowrap, by omega, by omega, by omega, Or.inr (Or.inr rfl), Or.inr (Or.inl (by omega)),
      by rw [restU.wr]; exact h.workspace.writable⟩
  have bitU := restU.gpr .r11 (by simp)
  rw [WP.seq_iff]
  refine WP.mono (selectAliasRow_ok u ctx (by omega) p0 p10 p12 count (by rw [bitU]; exact bit)) ?_
  intro v inv
  have value := inv.value
  have outside := inv.outside
  rw [memU, bitU, ← numAt_native, ← numAt_native, ← numAt_native] at value
  rw [memU, show 4 * (2 * w) = 8 * w by omega] at outside
  have frame := outside_workspace outside (size := 8 * len) (by omega)
  have keeps := outside_array_keeps outside (len := len) (by have := h.workspace.nowrap; omega)
  have restUV : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans
    (inv.rest.mono (by simp [roundClobbers, selectLoopClobbers]))
  refine WP.mono (restoreBase_ok v
    (by rw [restUV.rd, restUV.wr, restUV.sp]; exact h.stackRead)
    (saved_base_kept frame h.stackSep h.saved restUV.sp)) ?_
  rintro t ⟨ptr, memT, restT⟩
  rw [← memT] at frame keeps
  have rest := restUV.trans (restT.mono (by simp [roundClobbers]))
  exact ⟨(h.after_array (by decide : 6 ≠ 0) keeps frame rest ptr).1,
    by rw [memT]; exact value, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
