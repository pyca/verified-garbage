module
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState
public import VerifiedGarbage.Impl.Bignum.Arm.Exp

import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBit
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! # Execute an exponent bit and advance its byte-loop controls -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem expRound_ok (s : State) {base : BitVec 32} {len w M x E V c : Nat}
    (h : ExpState ok base len w M x E s) (hv : V < 2 ^ 32) (hc : 0 < c) (hc' : c < 2 ^ 32)
    (byte : s.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 V)
    (count : s.mem.readW (VG.Proof.Mont.off (State.addr base) 192) 32 = BitVec.ofNat 32 c) :
    WP isa expBitRound s fun t => ExpState ok base len w M x (2 * E + V / 128 % 2) t ∧
      t.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 (V + V) ∧
      t.mem.readW (VG.Proof.Mont.off (State.addr base) 192) 32 = BitVec.ofNat 32 (c - 1) ∧
      t.z = decide (c = 1) ∧
      (∀ d, d + 4 ≤ 192 → t.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32 =
        s.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32) ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 256 ≤ 8 * len := by
    have := h.ready.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  rw [expBitRound, WP.seq_iff]
  refine WP.mono (expBit_ok s h hv byte) ?_
  rintro u ⟨stateU, keepsU, frameU, restU⟩
  have byteU := (keeps_header_readW keepsU size (d := 200) (bits := 32) (by decide)).trans byte
  have countU := (keeps_header_readW keepsU size (d := 192) (bits := 32) (by decide)).trans count
  rw [WP.seq_iff]
  refine WP.mono (expShift_ok u stateU.ready.workspace (by omega) stateU.ready.ptr byteU) ?_
  rintro v ⟨memV, restV⟩
  obtain ⟨stateV, frameV⟩ := stateU.after_header (d := 200) (by decide) (by decide) memV restV
    ((restV.gpr .r0 (by decide)).trans stateU.ready.ptr)
  have byteV : v.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 (V + V) := by
    rw [memV, Mem.readW_writeW_self32]
  have countV : v.mem.readW (VG.Proof.Mont.off (State.addr base) 192) 32 = BitVec.ofNat 32 c := by
    have outside := writeW32_outside u.mem (State.addr base) (d := 200) (BitVec.ofNat 32 (V + V)) (by decide)
    rw [← memV] at outside
    rw [outside_read32 outside (d := 192) (by decide) (by decide)]
    exact countU
  refine WP.mono (expDecrement_ok v stateV.ready.workspace (by omega) stateV.ready.ptr hc hc' countV) ?_
  rintro t ⟨memT, flag, restT⟩
  obtain ⟨stateT, frameT⟩ := stateV.after_header (d := 192) (by decide) (by decide) memT restT
    ((restT.gpr .r0 (by decide)).trans stateV.ready.ptr)
  refine ⟨stateT, ?_, ?_, flag, ?_, frameU.trans (frameV.trans frameT),
    restU.trans ((restV.mono (by decide)).trans (restT.mono (by decide)))⟩
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
      outside_read32 outsideV (d := d) (by omega) (by omega),
      keeps_header_readW keepsU size (d := d) (bits := 32) (by omega)]

end VG.Proof.Bignum.Arm.ConditionalExp
