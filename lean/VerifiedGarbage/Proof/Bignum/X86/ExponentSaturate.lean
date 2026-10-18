module

public import VerifiedGarbage.Proof.Bignum.X86.ExponentAccumulate
public import VerifiedGarbage.Proof.Bignum.ExponentWords

/-! # Saturate only the public exponent's upper word -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem exponentSaturate_ok (s : State) {h : Nat}
    (high : s.gpr .edx = BitVec.ofNat 32 h) (zero : s.zf = some (decide (h < 2))) :
    WP isa (.ite .e (.block []) (.block [.mov .edx (.imm 2)])) s fun t =>
      t.gpr .edx = BitVec.ofNat 32 (min 2 h) ∧ t.mem = s.mem ∧ Keeps [.edx] s t := by
  refine WP.ite (decide (h < 2)) (by exact zero) ?_ ?_
  · intro valid
    have lt : h < 2 := of_decide_eq_true valid
    exact WP.block_nil ⟨by rw [high, Nat.min_eq_right (by omega)], rfl, Keeps.refl _ _⟩
  · intro invalid
    have ge : 2 ≤ h := by have := of_decide_eq_false invalid; omega
    refine wp_movS rfl fun t a _ => WP.block_nil ?_
    exact ⟨by rw [a.gpr, Nat.min_eq_left ge]; rfl, a.mem, a.keeps.mono (by decide)⟩

theorem exponentConsume_ok (s : State) {p : Addr} {x : Nat} {b : Byte}
    (ptr : s.ea ⟨.esi, 0⟩ = p)
    (read : InRegions (s.rd ++ s.wr) p 1) (byte : s.mem p = b)
    (low : s.gpr .ebx = BitVec.ofNat 32 (x % 2 ^ 32))
    (high : s.gpr .edx = BitVec.ofNat 32 (exponentHigh x)) :
    WP isa (.seq (.block exponentAccumulate)
      (.ite .e (.block []) (.block [.mov .edx (.imm 2)]))) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 ((256 * x + b.toNat) % 2 ^ 32) ∧
      t.gpr .edx = BitVec.ofNat 32 (exponentHigh (256 * x + b.toNat)) ∧
      t.mem = s.mem ∧ Keeps [.ebx, .edx, .ebp, .eax] s t := by
  rw [WP.seq_iff]
  refine WP.mono (exponentAccumulate_ok s ptr read) ?_
  rintro u ⟨lo, hi, zero, mem, rest⟩
  rw [low, byte, exponent_low_word] at lo
  rw [low, high, exponent_high_word] at hi zero
  rw [exponent_high_zero _ (by have := exponentHigh_bound x; have := Nat.mod_lt x (by decide : 0 < 2 ^ 32); omega)] at zero
  refine WP.mono (exponentSaturate_ok u hi zero) ?_
  rintro t ⟨value, memT, restT⟩
  rw [exponentHigh_step x b.toNat b.isLt] at value
  exact ⟨(restT.1 .ebx (by decide)).trans lo, value, memT.trans mem,
    (rest.mono (by decide)).trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.X86
