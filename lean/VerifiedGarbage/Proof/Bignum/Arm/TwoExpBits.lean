module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
public import VerifiedGarbage.Impl.Bignum.Arm.TwoExp

import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Framework.Block
/-! # Eight generator-two bit steps append one secret exponent byte -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/TwoExpRound.lean`, which only this module imported.
section

/-! # Advance a generator-two bit without secret-dependent control flow -/

section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem round_ok {base : BitVec 32} {len w M E V c : Nat} {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (s : State) (h : Power base len w M E s) (hp : P s)
    (hv : V < 2 ^ 32) (hc : 0 < c) (hc' : c < 2 ^ 32)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V)
    (count : s.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 c) :
    WP isa (VG.Impl.Bignum.Arm.TwoExp.round K.square K.twice) s fun t =>
      Power base len w M (2 * E + V / 128 % 2) t ∧ P t ∧
      t.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 (V + V) ∧
      t.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 (c - 1) ∧
      t.z = decide (c = 1) ∧
      (∀ d, d + 4 ≤ 192 → t.mem.readW (off (State.addr base) d) 32 =
        s.mem.readW (off (State.addr base) d) 32) ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 256 ≤ 8 * len := by
    have fits := h.ready.layout.2.2.1
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega
  rw [VG.Impl.Bignum.Arm.TwoExp.round, WP.seq_iff]
  refine WP.mono (bit_ok K s h hp hv byte) ?_
  rintro u ⟨stateU, pu, keepsU, frameU, restU⟩
  have byteU := (keepsU 200 (by decide)).trans byte
  have countU := (keepsU 192 (by decide)).trans count
  rw [WP.seq_iff]
  refine WP.mono (expShift_ok u stateU.ready.workspace (by omega) stateU.ready.ptr byteU) ?_
  rintro v ⟨memV, restV⟩
  obtain ⟨stateV, frameV⟩ := stateU.after_header (d := 200) (by decide) (by decide) memV restV
    ((restV.gpr .r0 (by decide)).trans stateU.ready.ptr)
  have rv : Rest roundClobbers u v := restV.mono (by decide)
  have pv := K.stable frameV rv pu
  have byteV : v.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 (V + V) := by
    rw [memV, Mem.readW_writeW_self32]
  have countV : v.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 c := by
    have outside := writeW32_outside u.mem (State.addr base) (d := 200) (BitVec.ofNat 32 (V + V)) (by decide)
    rw [← memV] at outside
    rw [outside_read32 outside (d := 192) (by decide) (by decide)]
    exact countU
  refine WP.mono (expDecrement_ok v stateV.ready.workspace (by omega) stateV.ready.ptr hc hc' countV) ?_
  rintro t ⟨memT, flag, restT⟩
  obtain ⟨stateT, frameT⟩ := stateV.after_header (d := 192) (by decide) (by decide) memT restT
    ((restT.gpr .r0 (by decide)).trans stateV.ready.ptr)
  have rt : Rest roundClobbers v t := restT.mono (by decide)
  refine ⟨stateT, K.stable frameT rt pv, ?_, ?_, flag, ?_,
    frameU.trans ((frameV.mono (by simpa using K.workspace)).trans
      (frameT.mono (by simpa using K.workspace))), restU.trans (rv.trans rt)⟩
  · have outside := writeW32_outside v.mem (State.addr base) (d := 192) (BitVec.ofNat 32 (c - 1)) (by decide)
    rw [← memT] at outside
    rw [outside_read32 outside (d := 200) (by decide) (by decide)]
    exact byteV
  · rw [memT, Mem.readW_writeW_self32]
  · intro d hd
    have outsideV := writeW32_outside u.mem (State.addr base) (d := 200) (BitVec.ofNat 32 (V + V)) (by decide)
    have outsideT := writeW32_outside v.mem (State.addr base) (d := 192) (BitVec.ofNat 32 (c - 1)) (by decide)
    rw [← memV] at outsideV
    rw [← memT] at outsideT
    rw [outside_read32 outsideT (d := d) (by omega) (by omega),
      outside_read32 outsideV (d := d) (by omega) (by omega), keepsU d (by omega)]

end VG.Proof.Bignum.Arm.TwoExp
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure BitState (base : BitVec 32) (len w M E v j : Nat) (s : State) : Prop where
  power : Power base len w M (E * 2 ^ j + v / 2 ^ (8 - j)) s
  byte : s.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 (v * 2 ^ j)
  count : s.mem.readW (VG.Proof.Mont.off (State.addr base) 192) 32 = BitVec.ofNat 32 (8 - j)

theorem bitState_step {base : BitVec 32} {len w M E v j : Nat} {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (s : State) (h : BitState base len w M E v j s) (hp : P s)
    (hv : v < 256) (hj : j < 8) :
    WP isa (VG.Impl.Bignum.Arm.TwoExp.round K.square K.twice) s fun t =>
      BitState base len w M E v (j + 1) t ∧ P t ∧ t.z = decide (j + 1 = 8) ∧
      (∀ d, d + 4 ≤ 192 → t.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32 =
        s.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32) ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have smallPow : 2 ^ j ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega : j ≤ 7)
  have valueFit : v * 2 ^ j < 2 ^ 32 := by
    have := Nat.mul_le_mul_left v smallPow
    omega
  refine WP.mono (round_ok K s h.power hp valueFit (by omega) (by omega) h.byte h.count) ?_
  rintro t ⟨power, pt, byte, count, zero, header, frame, rest⟩
  have expEq : 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
      E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) := by
    rw [Nat.mul_add, Nat.add_assoc, bit_step hj, show 7 - j = 8 - (j + 1) by omega,
      Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]
  rw [expEq] at power
  refine ⟨⟨power, ?_, ?_⟩, pt, ?_, header, frame, rest⟩
  · rw [byte, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
  · rw [count]; congr 1
  · rw [zero]; exact decide_eq_decide.mpr (by omega)

theorem bits_ok {base : BitVec 32} {len w M E v : Nat} {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (s : State) (h : BitState base len w M E v 0 s) (hp : P s)
    (hv : v < 256) :
    WP isa (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) s fun t =>
      Power base len w M (256 * E + v) t ∧ P t ∧
      (∀ d, d + 4 ≤ 192 → t.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32 =
        s.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32) ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ j, j + k = 8 ∧ 0 < k ∧ BitState base len w M E v j t ∧ P t ∧
    (∀ d, d + 4 ≤ 192 → t.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32 =
      s.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32) ∧
    Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  unfold VG.Impl.Bignum.Arm.TwoExp.bits
  refine WP.loop (M := isa) I ?_ 8 s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, state, pt, header, frame, rest⟩ := inv
    refine WP.mono (bitState_step K t state pt hv (by omega)) ?_
    rintro u ⟨next, pu, zero, headerU, frameU, restU⟩
    have headerAll := fun d hd => (headerU d hd).trans (header d hd)
    by_cases last : j + 1 = 8
    · left
      refine ⟨?_, ?_, pu, headerAll, frame.trans frameU, rest.trans restU⟩
      · change some (!u.z) = some false
        simp only [zero, last, decide_true, Bool.not_true]
      · have power := next.power
        simpa only [last, Nat.sub_self, Nat.pow_zero, Nat.div_one, show 2 ^ 8 = 256 from rfl,
          Nat.mul_comm E 256] using power
    · right
      refine ⟨?_, k - 1, by omega, j + 1, by omega, by omega, next, pu, headerAll,
        frame.trans frameU, rest.trans restU⟩
      change some (!u.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · exact ⟨0, by decide, by decide, h, hp, fun _ _ => rfl, Frame.refl _ _, Rest.refl _ _⟩

end VG.Proof.Bignum.Arm.TwoExp
