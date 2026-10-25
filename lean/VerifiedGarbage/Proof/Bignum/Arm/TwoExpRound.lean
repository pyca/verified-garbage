module

public import VerifiedGarbage.Impl.Bignum.Arm.TwoExp

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Framework.Block

/-! # Advance a generator-two bit without secret-dependent control flow -/

@[expose] public section

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
    simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes] at fits
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
