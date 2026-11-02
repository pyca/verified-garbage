module

public import VerifiedGarbage.Impl.Bignum.Arm.TwoExp

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpState
import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # A generic generator-two bit step

Arithmetic actions may write an additional callee-stack region. Their
persistent predicate records those calling conditions; the exponent loop
only assumes the stated power, header, frame, and register guarantees.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp op2_lsr op2_imm dpVal)

abbrev HeaderKept (base : BitVec 32) (s t : State) : Prop :=
  ∀ d, d + 4 ≤ 256 → t.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32

structure Kernel (base : BitVec 32) (len w : Nat) (P : State → Prop) (regions : List Region) where
  square : Prog isa
  twice : Prog isa
  workspace : (⟨State.addr base, 8 * len⟩ : Region) ∈ regions
  stable : ∀ {s t : State}, Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem →
    Rest roundClobbers s t → P s → P t
  square_ok : ∀ (s : State) (E : Nat) {M : Nat}, Power base len w M E s → P s →
    WP isa square s fun t => Power base len w M (2 * E) t ∧ P t ∧ HeaderKept base s t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  twice_ok : ∀ (s : State) (E : Nat) {M : Nat}, Power base len w M E s → P s →
    WP isa twice s fun t => Power base len w M E t ∧
      numAt t.mem (State.addr base) w 1 < M ∧
      numAt t.mem (State.addr base) w 1 % M = 2 ^ (E + 1) * 2 ^ (64 * w) % M ∧
      P t ∧ HeaderKept base s t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t

theorem digit_ok (s : State) {base : BitVec 32} {len w V : Nat}
    (h : ArithmeticReady base len w s) (hv : V < 2 ^ 32)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa (.block VG.Impl.Bignum.Arm.TwoExp.digit) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (V / 128 % 2) ∧ t.mem = s.mem ∧ Rest [.r11] s t := by
  have size : 256 ≤ 8 * len := by
    have fits := h.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega
  unfold VG.Impl.Bignum.Arm.TwoExp.digit
  refine wp_ldr (a := off (State.addr base) 200) (by decide)
    (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega))
    (h.workspace.read (by omega)) fun u a => ?_
  refine wp_mov (op2_lsr (by decide)) fun v b => ?_
  refine wp_dp (op2_imm (by decide)) fun t c => WP.block_nil ?_
  refine ⟨?_, c.mem.trans (b.mem.trans a.mem),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans (c.rest (by decide)))⟩
  rw [c.gpr, dpVal, b.gpr, a.gpr, byte]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  omega

theorem bit_ok {base : BitVec 32} {len w M E V : Nat} {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (s : State) (h : Power base len w M E s) (hp : P s)
    (hv : V < 2 ^ 32) (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa (VG.Impl.Bignum.Arm.TwoExp.bit K.square K.twice) s fun t =>
      Power base len w M (2 * E + V / 128 % 2) t ∧ P t ∧ HeaderKept base s t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.TwoExp.bit, WP.seq_iff]
  refine WP.mono (K.square_ok s E h hp) ?_
  rintro u ⟨powerU, pu, hdrU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (K.twice_ok u (2 * E) powerU pu) ?_
  rintro v ⟨powerV, boundV, valueV, pv, hdrV, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (digit_ok v powerV.ready hv ((hdrV 200 (by decide)).trans ((hdrU 200 (by decide)).trans byte))) ?_
  rintro z ⟨digit, memZ, restZ⟩
  have rz : Rest roundClobbers v z := restZ.mono (by decide)
  have powerZ := powerV.of_mem memZ restZ ((restZ.gpr .r0 (by decide)).trans powerV.ready.ptr)
  have frameZ : Frame [⟨State.addr base, 8 * len⟩] v.mem z.mem := by rw [memZ]; exact Frame.refl _ _
  have pz := K.stable frameZ rz pv
  have bitBound : V / 128 % 2 < 2 := Nat.mod_lt _ (by decide)
  have digitNat : (z.gpr .r11).toNat = V / 128 % 2 := by
    rw [digit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (selectArray_ok z powerZ.ready.workspace powerZ.ready.layout powerZ.ready.width
    powerZ.ready.ptr (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide)
    (by rw [digitNat]; omega) powerZ.ready.stackRead powerZ.ready.stackSep powerZ.ready.saved) ?_
  rintro t ⟨layoutT, widthT, selectT, outsideT, frameT, restT, ptrT⟩
  have keepsT := outside_array_keeps outsideT (len := len) (by have := powerZ.ready.workspace.nowrap; omega)
  have readyT := (powerZ.ready.after_array (by decide : 6 ≠ 0) keepsT frameT restT ptrT).1
  have fits : arrAt w 8 ≤ 8 * len := powerZ.ready.width ▸ powerZ.ready.layout.2.2.1
  have modulusT := (keeps_array_num keepsT fits (q := 0)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerZ.modulus
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have boundT : numAt t.mem (State.addr base) w 6 < M := by
    rw [selectT, digitNat]
    split
    · exact powerZ.bound
    · rw [memZ]; exact boundV
  have valueT : numAt t.mem (State.addr base) w 6 % M =
      2 ^ (2 * E + V / 128 % 2) * 2 ^ (64 * w) % M := by
    rw [selectT, digitNat]
    by_cases zero : V / 128 % 2 = 0
    · simp only [zero, ite_true, Nat.add_zero]
      exact powerZ.value
    · have one : V / 128 % 2 = 1 := by omega
      simp only [one, Nat.one_ne_zero, ite_false]
      rw [memZ]; exact valueV
  refine ⟨powerZ.after_y readyT modulusT keepsT boundT valueT, K.stable frameT restT pz, ?_,
    frameU.trans (frameV.trans ((frameZ.mono (by simpa using K.workspace)).trans
      (frameT.mono (by simpa using K.workspace)))), restU.trans (restV.trans (rz.trans restT))⟩
  intro d hd
  rw [keeps_header_readW keepsT size (d := d) (bits := 32) (by omega), memZ, hdrV d hd, hdrU d hd]

end VG.Proof.Bignum.Arm.TwoExp
