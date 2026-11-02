module
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareArgs
import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Block

/-! # Range checking does not require a prevalidated modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem arrayCompare_ok (s : State) {base : BitVec 32} {len w a b : Nat}
    (h : LayoutFrameReady base len w s) (ha : a < 8) (hb : b < 8) (na : a ≠ 3) (nb : b ≠ 3) :
    WP isa (arrayCompare a b) s fun t => LayoutFrameReady base len w t ∧
      t.gpr .r11 = (if numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w b then 1 else 0) ∧
      Keeps (State.addr base) len w 3 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have f0 := Nat.le_trans (array_end_le (w := w) hb) fits
  have f1 := Nat.le_trans (array_end_le (w := w) ha) fits
  have f3 := Nat.le_trans (array_end_le (w := w) (by decide : 3 < 8)) fits
  have sep1 := array_sep (w := w) na
  have sep0 := array_sep (w := w) nb
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  rw [arrayCompare, WP.seq_iff]
  refine WP.mono (arrayCompareArgs_ok s h.workspace size ha hb header h.ptr) ?_
  rintro u ⟨p0, p10, p12, count, borrow, memU, restU⟩
  have ctx : SubCtx u base (8 * len) (arrAt w 3) (arrAt w a) (arrAt w b) (2 * w) :=
    ⟨h.workspace.nowrap, by omega, by omega, by omega, by rcases sep1 with h | h <;> omega, by rcases sep0 with h | h <;> omega,
      by rw [restU.wr]; exact h.workspace.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (subCompare_ok u ctx (by omega) p0 p10 p12 count borrow) ?_
  rintro v ⟨value, outside, restV⟩
  rw [memU, ← numAt_native, ← numAt_native] at value
  rw [memU, show 4 * (2 * w) = 8 * w by omega] at outside
  have frame := outside_workspace outside (size := 8 * len) (by omega)
  have keeps := outside_array_keeps outside (len := len) (by have := h.workspace.nowrap; omega)
  have restUV : Rest roundClobbers s v := (restU.mono (by decide)).trans
    (restV.mono (by decide))
  refine WP.mono (restoreBase_ok v
    (by rw [restUV.rd, restUV.wr, restUV.sp]; exact h.stackRead)
    (saved_base_kept frame h.stackSep h.saved restUV.sp)) ?_
  rintro t ⟨ptr, memT, restT⟩
  rw [← memT] at frame keeps
  have rest := restUV.trans (restT.mono (by decide))
  exact ⟨h.after_array keeps frame rest ptr,
    (restT.gpr .r11 (by decide)).trans value, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
