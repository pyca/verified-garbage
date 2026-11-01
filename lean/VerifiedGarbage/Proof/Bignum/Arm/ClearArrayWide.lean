module

import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.ClearOperandBuffer
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge

/-! # Clear an arithmetic result including its native carry words -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem outside_array_prefix_keeps {m m' : Mem} {base : Addr} {len w o n : Nat}
    (outside : Outside base (arrAt w o) n m m') (size : 8 * len < 2 ^ 64)
    (fits : n ≤ 8 * (w + 2)) : Keeps base len w o m m' := by
  intro i hi separate
  have sep := separate o (by simp)
  apply outside
  change (base + BitVec.ofNat 64 i - base).toNat < arrAt w o ∨
    arrAt w o + n ≤ (base + BitVec.ofNat 64 i - base).toNat
  rw [Mem.sub_ofNat_toNat _ (by omega)]
  omega

theorem clearArrayWide_ok (s : State) {base : BitVec 32} {len w o : Nat}
    (h : ArithmeticReady base len w s) (ho : o < 8) (ho0 : o ≠ 0) :
    WP isa (clearOperandBuffer (64 + 8 * o)) s fun t => ArithmeticReady base len w t ∧
      val32 t.mem (State.addr base) (arrAt w o) (2 * w + 2) = 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have bound := Nat.le_trans (array_end_le ho) fits
  have small : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have nowrap := h.workspace.nowrap
  have header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  refine WP.mono (clearOperandBuffer_ok s h.workspace (by omega) (by omega) (by omega)
    (by omega) h.ptr header.count (header.array o ho) h.stackRead h.stackSep h.saved) ?_
  rintro t ⟨zero, outside, frame, ptr, rest⟩
  have keeps := outside_array_prefix_keeps outside (by omega : 8 * len < 2 ^ 64) (by omega)
  exact ⟨(h.after_array ho0 keeps frame rest ptr).1, zero, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
