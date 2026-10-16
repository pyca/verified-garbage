module

public import VerifiedGarbage.Proof.Bignum.Arm.ExpByte
public import VerifiedGarbage.Proof.Bignum.Arm.ExpByteCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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

theorem ExpByteState.input {s : State} {base ep : BitVec 32} {len w M x j : Nat} {eb : List Byte}
    (h : ExpByteState base ep len w M x eb j s) (hj : j < eb.length) :
    ExpByteInput base (ep + BitVec.ofNat 32 j) len w M x (pre eb j) eb[j] s := by
  have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
    addr_add (by have := h.sourceFit; omega)
  refine ⟨h.power, h.pointer, ?_, ?_⟩
  · rw [address]
    exact CallLay.inRegions_sub h.read (by omega) (by have := h.countFit; omega)
  · rw [address]; exact h.bytes j hj

theorem expByteState_step (s : State) {base ep : BitVec 32} {len w M x j : Nat} {eb : List Byte}
    (h : ExpByteState base ep len w M x eb j s) (hj : j < eb.length) :
    WP isa (.seq expByteHead (.seq expBits (.block expByteNext))) s fun t =>
      ExpByteState base ep len w M x eb (j + 1) t ∧ t.z = decide (j + 1 = eb.length) := by
  have input := h.input hj
  refine WP.mono (expByte_ok s h.power (by omega) (by have := h.countFit; omega)
    h.pointer h.count input.read) ?_
  rintro t ⟨power, pointer, count, zero, frame, rest⟩
  rw [input.byte] at power
  have prefixEq : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
    rw [pre_succ eb hj, Nat.mul_comm]
  rw [prefixEq] at power
  refine ⟨⟨power, ?_, ?_, h.countFit, h.sourceFit, ?_, h.separate, ?_⟩, ?_⟩
  · rw [pointer]
    change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [count]; congr 1
  · rw [rest.rd, rest.wr]; exact h.read
  · intro i hi
    rw [frame.bytes (R := ⟨State.addr ep, eb.length⟩)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate)
      (by change eb.length ≤ 2 ^ 64; have := h.countFit; omega) hi]
    exact h.bytes i hi
  · rw [zero]; exact decide_eq_decide.mpr (by omega)

end VG.Proof.Bignum.Arm
