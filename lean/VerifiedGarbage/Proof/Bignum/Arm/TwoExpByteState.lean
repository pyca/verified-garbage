module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Bignum.Arm.TwoExp
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpByte
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # A public exponent-buffer position with secret exponent bytes -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure ByteInput (base ep : BitVec 32) (len w M E : Nat) (b : Byte) (s : State) : Prop where
  power : Power base len w M E s
  pointer : s.mem.readW (off (State.addr base) 128) 32 = ep
  read : InRegions (s.rd ++ s.wr) (State.addr ep) 1
  byte : s.mem (State.addr ep) = b

structure ByteState (base ep : BitVec 32) (len w M : Nat) (P : State → Prop)
    (regions : List Region) (eb : List Byte) (j : Nat) (s : State) : Prop where
  power : Power base len w M (pre eb j) s
  persistent : P s
  pointer : s.mem.readW (off (State.addr base) 128) 32 = ep + BitVec.ofNat 32 j
  count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 (eb.length - j)
  countFit : eb.length < 2 ^ 32
  sourceFit : ep.toNat + eb.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length
  separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r
  bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i]

theorem ByteState.input {s : State} {base ep : BitVec 32} {len w M j : Nat}
    {P : State → Prop} {regions : List Region} {eb : List Byte}
    (h : ByteState base ep len w M P regions eb j s) (hj : j < eb.length) :
    ByteInput base (ep + BitVec.ofNat 32 j) len w M (pre eb j) eb[j] s := by
  have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
    addr_add (by have := h.sourceFit; omega)
  refine ⟨h.power, h.pointer, ?_, ?_⟩
  · rw [address]
    exact CallLay.inRegions_sub h.read (by omega) (by have := h.countFit; omega)
  · rw [address]; exact h.bytes j hj

theorem byteState_step {base ep : BitVec 32} {len w M j : Nat} {P : State → Prop}
    {regions : List Region} {eb : List Byte}
    (K : Kernel base len w P regions) (s : State) (h : ByteState base ep len w M P regions eb j s)
    (hj : j < eb.length) :
    WP isa (.seq VG.Impl.Bignum.Arm.expByteHead
      (.seq (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) (.block VG.Impl.Bignum.Arm.expByteNext))) s fun t =>
      ByteState base ep len w M P regions eb (j + 1) t ∧ t.z = decide (j + 1 = eb.length) ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have input := h.input hj
  refine WP.mono (byte_ok K s h.power h.persistent (by omega) (by have := h.countFit; omega)
    h.pointer h.count input.read) ?_
  rintro t ⟨power, persistent, pointer, count, zero, frame, rest⟩
  rw [input.byte] at power
  have prefixEq : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
    rw [pre_succ eb hj, Nat.mul_comm]
  rw [prefixEq] at power
  refine ⟨⟨power, persistent, ?_, ?_, h.countFit, h.sourceFit, ?_, h.separate, ?_⟩, ?_, frame, rest⟩
  · rw [pointer]
    change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [count]; congr 1
  · rw [rest.rd, rest.wr]; exact h.read
  · intro i hi
    rw [frame.bytes h.separate (by change eb.length ≤ 2 ^ 64; have := h.countFit; omega) hi]
    exact h.bytes i hi
  · rw [zero]; exact decide_eq_decide.mpr (by omega)

end VG.Proof.Bignum.Arm.TwoExp
