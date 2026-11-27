module

import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpInit
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteState
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBytes

/-! # The complete inputs for native RSA exponentiation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
variable {ok : Prop} {Q : State → Prop} {regions : List Region}

structure ExpPhaseInput (ok : Prop) (base ep : BitVec 32) (len w M x : Nat) (eb : List Byte) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = M
  odd : M % 2 = 1
  input : numAt s.mem (State.addr base) w 1 = x
  r2bound : numAt s.mem (State.addr base) w 4 < M
  r2value : ok → numAt s.mem (State.addr base) w 4 % M = 2 ^ (64 * w) * 2 ^ (64 * w) % M
  pointer : s.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep
  count : s.mem.readW (VG.Proof.Mont.off (State.addr base) 132) 32 = BitVec.ofNat 32 eb.length
  positive : 0 < eb.length
  countFit : eb.length < 2 ^ 32
  sourceFit : ep.toNat + eb.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length
  separate : Region.Disjoint ⟨State.addr ep, eb.length⟩ ⟨State.addr base, 8 * len⟩
  bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i]

theorem expPhase_init_ready (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (K : TwoExp.Montgomery base len w Q regions) (h : ExpPhaseInput ok base ep len w M x eb s) (q : Q s)
    (sepR : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (expInitWith K.op) s fun t => (ExpByteState ok base ep len w M x eb 0 t ∧ Q t) ∧
      Frame regions s.mem t.mem ∧ VG.Proof.X25519.Arm.Rest roundClobbers s t := by
  refine WP.mono (expInit_ok s K h.ready q h.modulus h.odd h.input h.r2bound h.r2value) ?_
  rintro t ⟨power, qt, header, frame, rest⟩
  refine ⟨⟨⟨power, ?_, ?_, h.countFit, h.sourceFit, ?_, h.separate, ?_⟩, qt⟩, frame, rest⟩
  · rw [header 128 (by decide), BitVec.add_zero]; exact h.pointer
  · rw [header 132 (by decide)]; exact h.count
  · rw [rest.rd, rest.wr]; exact h.read
  · intro i hi
    rw [frame.bytes (R := ⟨State.addr ep, eb.length⟩) (fun r hr => sepR r hr)
      (by change eb.length ≤ 2 ^ 64; have := h.countFit; omega_using [this]) hi]
    exact h.bytes i hi

theorem expPhase_bytes_ready (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (K : TwoExp.Montgomery base len w Q regions) (h : ExpByteState ok base ep len w M x eb 0 s) (q : Q s)
    (positive : 0 < eb.length) (sepR : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (expBytesWith K.op) s fun t => ExpState ok base len w M x (Spec.Rsa.os2ip eb) t ∧ Q t ∧
      Frame regions s.mem t.mem ∧ VG.Proof.X25519.Arm.Rest roundClobbers s t :=
  expBytes_ok s K h.power q positive h.countFit h.sourceFit h.read sepR h.bytes
    (by simpa only [BitVec.add_zero] using h.pointer) h.count

end VG.Proof.Bignum.Arm.ConditionalExp
