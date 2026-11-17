module

public import VerifiedGarbage.Impl.Bignum.X86.ExponentCheck
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.ExponentAccumulate
import VerifiedGarbage.Proof.Bignum.ExponentWords

/-! ### `Bignum.X86.ExponentSaturate`, which this module and modules that import it used -/

section

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
    exact WP.block_nil ⟨by rw [high, Nat.min_eq_right (by omega_using [lt])], rfl, Keeps.refl _ _⟩
  · intro invalid
    have ge : 2 ≤ h := by have := of_decide_eq_false invalid; omega_using [this]
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
  rw [exponent_high_zero _ (by have := exponentHigh_bound x; have := Nat.mod_lt x (by decide : 0 < 2 ^ 32); omega_arith)] at zero
  refine WP.mono (exponentSaturate_ok u hi zero) ?_
  rintro t ⟨value, memT, restT⟩
  rw [exponentHigh_step x b.toNat b.isLt] at value
  exact ⟨(restT.1 .ebx (by decide)).trans lo, value, memT.trans mem,
    (rest.mono (by decide)).trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.X86

end

end

/-! # Consume one public exponent byte and advance the public scan -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem exponentAdvance_ok (s : State) {c : Nat} (hc : 0 < c) (hc' : c < 2 ^ 32)
    (count : s.gpr .ecx = BitVec.ofNat 32 c) :
    WP isa (.block exponentAdvance) s fun t => t.gpr .esi = s.gpr .esi + 1 ∧
      t.gpr .ecx = BitVec.ofNat 32 (c - 1) ∧ t.zf = some (decide (c = 1)) ∧
      t.mem = s.mem ∧ Keeps [.esi, .ecx] s t := by
  unfold exponentAdvance
  refine wp_addS rfl fun u a _ => ?_
  refine wp_subS rfl fun v b _ => ?_
  refine wp_cmpS rfl fun t f z => WP.block_nil ?_
  have value : u.gpr .ecx - (1 : BitVec 32) = BitVec.ofNat 32 (c - 1) := by
    rw [a.other .ecx (by decide), count, Dynamic.counter_sub hc' hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [f.gpr, b.other .esi (by decide), a.gpr]
  · rw [f.gpr, b.gpr, value]
  · rw [z, b.gpr, a.other .ecx (by decide), count, Dynamic.counter_sub hc' hc, Dynamic.counter_zero hc' hc]
  · rw [f.mem, b.mem, a.mem]
  · exact ((a.keeps.mono (by decide)).widen b.keeps).trans (f.keeps _)

theorem exponentByte_ok (s : State) {p : BitVec 32} {x c : Nat} {b : Byte}
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (ptr : s.gpr .esi = p) (count : s.gpr .ecx = BitVec.ofNat 32 c)
    (read : InRegions (s.rd ++ s.wr) (byteAddr p) 1) (byte : s.mem (byteAddr p) = b)
    (low : s.gpr .ebx = BitVec.ofNat 32 (x % 2 ^ 32))
    (high : s.gpr .edx = BitVec.ofNat 32 (exponentHigh x)) :
    WP isa exponentByte s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 ((256 * x + b.toNat) % 2 ^ 32) ∧
      t.gpr .edx = BitVec.ofNat 32 (exponentHigh (256 * x + b.toNat)) ∧
      t.gpr .esi = p + 1 ∧ t.gpr .ecx = BitVec.ofNat 32 (c - 1) ∧ t.zf = some (decide (c = 1)) ∧
      t.mem = s.mem ∧ Keeps [.esi, .ebx, .edx, .ebp, .eax, .ecx] s t := by
  rw [exponentByte, WP.seq_iff]
  refine WP.mono (exponentConsume_ok s (by simp only [State.ea, ptr, BitVec.add_zero]; rfl) read byte low high) ?_
  rintro u ⟨lowU, highU, memU, restU⟩
  refine WP.mono (exponentAdvance_ok u hc hc' ((restU.1 .ecx (by decide)).trans count)) ?_
  rintro t ⟨ptrT, countT, zero, memT, restT⟩
  exact ⟨(restT.1 .ebx (by decide)).trans lowU, (restT.1 .edx (by decide)).trans highU,
    by rw [ptrT, restU.1 .esi (by decide), ptr], countT, zero, memT.trans memU,
    (restU.mono (by decide)).trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.X86
