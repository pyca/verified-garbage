module
public import VerifiedGarbage.Impl.Bignum.Arm.SelectArray
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Branchless workspace selection also permits replacing the modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

theorem array_select_separate (w o a : Nat) :
    arrAt w o + 4 * (2 * w) ≤ arrAt w a ∨ arrAt w a + 4 * (2 * w) ≤ arrAt w o ∨ arrAt w o = arrAt w a := by
  rcases Nat.lt_trichotomy o a with lt | eq | gt
  · left; have := array_end_le (w := w) lt; omega
  · right; right; rw [eq]
  · right; left; have := array_end_le (w := w) gt; omega

theorem selectArray_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ptr : s.gpr .r0 = base)
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (bit : (s.gpr .r11).toNat ≤ 1)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa (selectArray o a b) s fun t =>
      Layout t.mem (State.addr base) len ∧ wOf t.mem (State.addr base) = w ∧
      numAt t.mem (State.addr base) w o = (if (s.gpr .r11).toNat = 0 then
        numAt s.mem (State.addr base) w a else numAt s.mem (State.addr base) w b) ∧
      Outside (State.addr base) (arrAt w o) (8 * w) s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t ∧ t.gpr .r0 = base := by
  have hw : 2 ≤ w := width ▸ layout.1
  have fits : arrAt w 8 ≤ 8 * len := width ▸ layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have fo := Nat.le_trans (array_end_le (w := w) ho) fits
  have fa := Nat.le_trans (array_end_le (w := w) ha) fits
  have fb := Nat.le_trans (array_end_le (w := w) hb) fits
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) layout
  rw [width] at header
  rw [selectArray, WP.seq_iff]
  refine WP.mono (selectArrayArgs_ok s ho ha hb ws size header ptr) ?_
  rintro u ⟨p0, p10, p12, count, memU, restU⟩
  have ctx : SelectCtx u base (8 * len) (arrAt w o) (arrAt w a) (arrAt w b) (2 * w) :=
    ⟨ws.nowrap, by omega, by omega, by omega, array_select_separate w o a, array_select_separate w o b,
      by rw [restU.wr]; exact ws.writable⟩
  have bitU := restU.gpr .r11 (by decide)
  rw [WP.seq_iff]
  refine WP.mono (selectAliasRow_ok u ctx (by omega) p0 p10 p12 count (by rw [bitU]; exact bit)) ?_
  intro v inv
  have value := inv.value
  have outside := inv.outside
  rw [memU, bitU, ← numAt_native, ← numAt_native, ← numAt_native] at value
  rw [memU, show 4 * (2 * w) = 8 * w by omega] at outside
  have frame := outside_workspace outside (size := 8 * len) (by omega)
  have keeps := outside_array_keeps outside (len := len) (by have := ws.nowrap; omega)
  have kl := keeps_layout layout (by rw [width]; exact keeps)
  have restUV : Rest roundClobbers s v := (restU.mono (by decide)).trans
    (inv.rest.mono (by decide))
  refine WP.mono (restoreBase_ok v
    (by rw [restUV.rd, restUV.wr, restUV.sp]; exact stackRead)
    (saved_base_kept frame stackSep saved restUV.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  exact ⟨by rw [memT]; exact kl.2, by rw [memT]; exact kl.1.trans width,
    by rw [memT]; exact value, by rw [memT]; exact outside, by rw [memT]; exact frame,
    restUV.trans (restT.mono (by decide)), ptrT⟩

end VG.Proof.Bignum.Arm
