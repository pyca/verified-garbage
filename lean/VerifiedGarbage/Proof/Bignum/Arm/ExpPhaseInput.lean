module

import VerifiedGarbage.Proof.Bignum.Arm.ExpInit
public import VerifiedGarbage.Proof.Bignum.Arm.ExpByteState
import VerifiedGarbage.Proof.Bignum.Arm.ExpBytes

/-! # The complete inputs for native RSA exponentiation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

structure ExpPhaseInput (base ep : BitVec 32) (len w M x : Nat) (eb : List Byte) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = M
  odd : M % 2 = 1
  input : numAt s.mem (State.addr base) w 1 = x
  r2bound : numAt s.mem (State.addr base) w 4 < M
  r2value : numAt s.mem (State.addr base) w 4 % M = 2 ^ (64 * w) * 2 ^ (64 * w) % M
  pointer : s.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep
  count : s.mem.readW (VG.Proof.Mont.off (State.addr base) 132) 32 = BitVec.ofNat 32 eb.length
  positive : 0 < eb.length
  countFit : eb.length < 2 ^ 32
  sourceFit : ep.toNat + eb.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length
  separate : Region.Disjoint ⟨State.addr ep, eb.length⟩ ⟨State.addr base, 8 * len⟩
  bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i]

theorem expPhase_init_ready (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (h : ExpPhaseInput base ep len w M x eb s) :
    WP isa expInit s fun t => ExpByteState base ep len w M x eb 0 t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ VG.Proof.X25519.Arm.Rest roundClobbers s t := by
  refine WP.mono (expInit_ok s h.ready h.modulus h.odd h.input h.r2bound h.r2value) ?_
  rintro t ⟨power, header, frame, rest⟩
  refine ⟨⟨power, ?_, ?_, h.countFit, h.sourceFit, ?_, h.separate, ?_⟩, frame, rest⟩
  · rw [header 128 (by decide), BitVec.add_zero]; exact h.pointer
  · rw [header 132 (by decide)]; exact h.count
  · rw [rest.rd, rest.wr]; exact h.read
  · intro i hi
    rw [frame.bytes (R := ⟨State.addr ep, eb.length⟩)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate)
      (by change eb.length ≤ 2 ^ 64; have := h.countFit; omega) hi]
    exact h.bytes i hi

theorem expPhase_bytes_ready (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (h : ExpByteState base ep len w M x eb 0 s) (positive : 0 < eb.length) :
    WP isa expBytes s fun t => ExpState base len w M x (Spec.Rsa.os2ip eb) t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ VG.Proof.X25519.Arm.Rest roundClobbers s t :=
  expBytes_ok s h.power positive h.countFit h.sourceFit h.read h.separate h.bytes
    (by simpa only [BitVec.add_zero] using h.pointer) h.count

end VG.Proof.Bignum.Arm
