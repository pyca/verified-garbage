module

public import VerifiedGarbage.Proof.Bignum.Arm.ExponentAccumulate
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentWords
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Saturate only the public exponent's upper word -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem exponentSaturate_ok (s : State) {h : Nat}
    (high : s.gpr .r4 = BitVec.ofNat 32 h) (zero : s.z = decide (h < 2)) :
    WP isa (.ite .eq (.block []) (.block [.mov .r4 (.imm 2)])) s fun t =>
      t.gpr .r4 = BitVec.ofNat 32 (min 2 h) ∧ t.mem = s.mem ∧ Rest [.r4] s t := by
  refine WP.ite (decide (h < 2)) (by change some s.z = _; rw [zero]) ?_ ?_
  · intro valid
    have lt : h < 2 := of_decide_eq_true valid
    exact WP.block_nil ⟨by rw [high, Nat.min_eq_right (by omega)], rfl, Rest.refl _ _⟩
  · intro invalid
    have ge : 2 ≤ h := by have := of_decide_eq_false invalid; omega
    refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
    exact ⟨by rw [a.gpr, Nat.min_eq_left ge]; rfl, a.mem, a.rest (by simp)⟩

theorem exponentConsume_ok (s : State) {p : Addr} {x : Nat} {b : Byte}
    (ptr : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) = p)
    (read : InRegions (s.rd ++ s.wr) p 1) (byte : s.mem p = b)
    (low : s.gpr .r3 = BitVec.ofNat 32 (x % 2 ^ 32))
    (high : s.gpr .r4 = BitVec.ofNat 32 (exponentHigh x)) :
    WP isa (.seq (.block exponentAccumulate)
      (.ite .eq (.block []) (.block [.mov .r4 (.imm 2)]))) s fun t =>
      t.gpr .r3 = BitVec.ofNat 32 ((256 * x + b.toNat) % 2 ^ 32) ∧
      t.gpr .r4 = BitVec.ofNat 32 (exponentHigh (256 * x + b.toNat)) ∧
      t.mem = s.mem ∧ Rest [.r3, .r4, .r5, .r7] s t := by
  rw [WP.seq_iff]
  refine WP.mono (exponentAccumulate_ok s ptr read) ?_
  rintro u ⟨lo, hi, zero, mem, rest⟩
  rw [low, byte, exponent_low_word] at lo
  rw [low, high, exponent_high_word] at hi zero
  rw [exponent_high_zero _ (by have := exponentHigh_bound x; have := Nat.mod_lt x (by decide : 0 < 2 ^ 32); omega)] at zero
  refine WP.mono (exponentSaturate_ok u hi zero) ?_
  rintro t ⟨value, memT, restT⟩
  rw [exponentHigh_step x b.toNat b.isLt] at value
  exact ⟨(restT.gpr .r3 (by simp)).trans lo, value, memT.trans mem,
    rest.trans (restT.mono (by simp))⟩

end VG.Proof.Bignum.Arm
