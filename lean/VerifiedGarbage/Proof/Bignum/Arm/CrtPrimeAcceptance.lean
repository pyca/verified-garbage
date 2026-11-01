module

import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptance
public import VerifiedGarbage.Proof.Bignum.Arm.PreparePrime
public import VerifiedGarbage.Impl.Bignum.Arm.CrtAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge

/-! # The saved validation bit establishes the sanitized-factor precondition -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_primeAcceptance_ready (s : State) {base : BitVec 32} {len w : Nat}
    (h : LayoutFrameReady base len w s) (stackFit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4)
    (bit : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1)
    (valid : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 →
      1 < numAt s.mem (State.addr base) w 0 ∧ numAt s.mem (State.addr base) w 0 % 2 = 1) :
    WP isa (.block installAcceptance) s fun t => PrimeInput base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      (t.mem.readW (off (State.addr base) 212) 32) = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest [.r11, .r12] s t := by
  have fit : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have small : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega
  have nowrap := h.workspace.nowrap
  refine WP.mono (crt_installAcceptance_ok s h.workspace (by omega) h.ptr stackFit read) ?_
  rintro t ⟨mem, outside, rest⟩
  have kl := control_outside_layout (by decide : 128 ≤ 212) outside h.layout
  have frame := outside_workspace outside (by omega : 212 + 4 ≤ 8 * len)
  have number : numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
    have bound := Nat.le_trans (array_end_le (w := w) (j := 0) (by decide : 0 < 8)) fit
    rw [numAt_native, numAt_native]
    apply outside.val32
    · right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
    · omega
  have value : t.mem.readW (off (State.addr base) 212) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [mem, Mem.readW_writeW_self32]
  refine ⟨⟨⟨⟨h.workspace.congr rest.wr, kl.2, kl.1.trans h.width,
    (rest.gpr .r0 (by simp)).trans h.ptr⟩, ?_, ?_, ?_⟩, ?_, ?_⟩, number, value, frame, rest⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp
  · rw [value]; exact bit
  · rw [value, number]; exact valid

end VG.Proof.Bignum.Arm
