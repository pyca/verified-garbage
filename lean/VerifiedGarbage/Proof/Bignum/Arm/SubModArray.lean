module

public import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
public import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayArgs
public import VerifiedGarbage.Proof.Bignum.Arm.SubModBuffers
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Modular subtraction preserves the shared workspace invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem subModArray_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (ho0 : o ≠ 0) (hoa : o ≠ a) (hob : o ≠ b)
    (boundA : numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0)
    (boundB : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (subModArray o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w o =
        (numAt s.mem (State.addr base) w a + numAt s.mem (State.addr base) w 0 -
          numAt s.mem (State.addr base) w b) % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have endO := Nat.le_trans (array_end_le ho.1) fits
  have endA := Nat.le_trans (array_end_le ha.1) fits
  have endB := Nat.le_trans (array_end_le hb.1) fits
  have endM := Nat.le_trans (array_end_le (w := w) (j := 0) (by decide : 0 < 8)) fits
  have small : 256 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
  have nowrap := h.workspace.nowrap
  have width : 2 ≤ w := h.width ▸ h.layout.1
  have sepA := array_sep (w := w) hoa
  have sepB := array_sep (w := w) hob
  have sepM := array_sep (w := w) ho0
  rw [subModArray, WP.seq_iff]
  refine WP.mono (clearArrayWide_ok s h ho.1 ho0) ?_
  rintro u ⟨readyU, zero, keepsU, frameU, restU⟩
  have oldA := keeps_array_num keepsU fits ha (Ne.symm hoa)
  have oldB := keeps_array_num keepsU fits hb (Ne.symm hob)
  have oldM := keeps_array_num keepsU fits (q := 0)
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (Ne.symm ho0)
  have high : val32 u.mem (State.addr base) (arrAt w o + 4 * (2 * w)) 2 = 0 := by
    rw [val32_append] at zero
    have positive : 0 < 2 ^ (32 * (2 * w)) := Nat.two_pow_pos _
    have mul : 2 ^ (32 * (2 * w)) * val32 u.mem (State.addr base) (arrAt w o + 4 * (2 * w)) 2 = 0 := by omega
    rcases Nat.mul_eq_zero.mp mul with bad | good
    · omega
    · exact good
  have header := nativeHeader_of_layout u.mem base nowrap (Nat.le_refl _) readyU.layout
  rw [readyU.width] at header
  rw [WP.seq_iff]
  refine WP.mono (subModArrayArgs_ok u ho.1 ha.1 hb.1 readyU.workspace (by omega) header readyU.ptr) ?_
  rintro v ⟨p0, p10, p12, p9, count, memV, restV⟩
  have ctx : SubCtx v base (8 * len) (arrAt w o) (arrAt w a) (arrAt w b) (2 * w) :=
    ⟨nowrap, by omega, by omega, by omega, by omega, by omega,
      by rw [restV.wr]; exact readyU.workspace.writable⟩
  have row : RowCtx v base (8 * len) (arrAt w o) (arrAt w 0) (2 * w) :=
    ⟨nowrap, by omega, by omega, by omega, by rw [restV.wr]; exact readyU.workspace.writable⟩
  have nums (q : Nat) : val32 v.mem (State.addr base) (arrAt w q) (2 * w) = numAt u.mem (State.addr base) w q := by
    rw [memV, numAt_native]
  rw [WP.seq_iff]
  refine WP.mono (subModBuffers_ok v ctx row (by omega) (by omega) p0 p10 p12 p9 count
    (by rw [memV]; exact high) (by rw [nums a, nums 0, oldA, oldM]; exact boundA)
    (by rw [nums b, nums 0, oldB, oldM]; exact boundB)) ?_
  rintro z ⟨value, _, outside, restZ⟩
  rw [nums a, nums b, nums 0, oldA, oldB, oldM] at value
  rw [memV] at outside
  have frameZ := outside_workspace outside (by omega : arrAt w o + 4 * (2 * w + 2) ≤ 8 * len)
  have keepsZ := outside_array_prefix_keeps outside (by omega : 8 * len < 2 ^ 64) (by omega)
  have restUZ : Rest roundClobbers u z := (restV.mono (by simp [roundClobbers])).trans restZ
  refine WP.mono (restoreBase_ok z (by rw [restUZ.rd, restUZ.wr, restUZ.sp]; exact readyU.stackRead)
    (saved_base_kept frameZ readyU.stackSep readyU.saved restUZ.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  rw [← memT] at keepsZ frameZ
  have rest : Rest roundClobbers u t := restUZ.trans (restT.mono (by simp [roundClobbers]))
  exact ⟨(readyU.after_array ho0 keepsZ frameZ rest ptrT).1,
    by rw [numAt_native, memT]; exact value,
    fun i hi sep => (keepsZ i hi sep).trans (keepsU i hi sep), frameU.trans frameZ, restU.trans rest⟩

end VG.Proof.Bignum.Arm
