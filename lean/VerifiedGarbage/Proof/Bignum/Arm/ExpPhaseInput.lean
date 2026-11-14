module

import VerifiedGarbage.Proof.Bignum.Arm.ExpInit
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Arm.ExpBitTest
import VerifiedGarbage.Proof.Bignum.Arm.ExpStep
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteLoad
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
import VerifiedGarbage.Impl.Bignum.Arm.Square
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Bignum.Arm.ExpByteState`, which only this module used -/

section

/-! # Public buffer invariants for the exponent-byte timing proof -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure ExpByteState (base ep : BitVec 32) (len w M x : Nat) (eb : List Byte) (j : Nat) (s : State) : Prop where
  power : ExpState base len w M x (pre eb j) s
  pointer : s.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep + BitVec.ofNat 32 j
  count : s.mem.readW (VG.Proof.Mont.off (State.addr base) 132) 32 = BitVec.ofNat 32 (eb.length - j)
  countFit : eb.length < 2 ^ 32
  sourceFit : ep.toNat + eb.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length
  separate : Region.Disjoint ⟨State.addr ep, eb.length⟩ ⟨State.addr base, 8 * len⟩
  bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i]

end VG.Proof.Bignum.Arm

end

end


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
      (by change eb.length ≤ 2 ^ 64; have := h.countFit; omega_using [this]) hi]
    exact h.bytes i hi

end VG.Proof.Bignum.Arm
