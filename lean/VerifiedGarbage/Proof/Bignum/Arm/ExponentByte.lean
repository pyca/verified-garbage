module

public import VerifiedGarbage.Proof.Bignum.Arm.ExponentSaturate
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Consume one public exponent byte and advance the public scan -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_dp wp_subs op2_imm dpVal ofNat_beq_zero)

theorem exponentAdvance_ok (s : State) {c : Nat} (hc : 0 < c) (hc' : c < 2 ^ 32)
    (count : s.gpr .lr = BitVec.ofNat 32 c) :
    WP isa (.block exponentAdvance) s fun t => t.gpr .r1 = s.gpr .r1 + 1 ∧
      t.gpr .lr = BitVec.ofNat 32 (c - 1) ∧ t.z = decide (c = 1) ∧
      t.mem = s.mem ∧ Rest [.r1, .lr] s t := by
  unfold exponentAdvance
  refine wp_dp (op2_imm (by decide)) fun u a => ?_
  refine wp_subs (op2_imm (by decide)) fun t b zero => WP.block_nil ?_
  have value : u.gpr .lr - (1 : BitVec 32) = BitVec.ofNat 32 (c - 1) := by
    rw [a.other .lr (by decide), count]
    change BitVec.ofNat 32 c - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
  exact ⟨by rw [b.other .r1 (by decide), a.gpr]; rfl, b.gpr.trans value,
    by rw [zero, value, ofNat_beq_zero (by omega)]; exact decide_eq_decide.mpr (by omega),
    b.mem.trans a.mem, (a.rest (by simp)).trans (b.rest (by simp))⟩

theorem exponentByte_ok (s : State) {p : BitVec 32} {x c : Nat} {b : Byte}
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (ptr : s.gpr .r1 = p) (count : s.gpr .lr = BitVec.ofNat 32 c)
    (read : InRegions (s.rd ++ s.wr) (State.addr p) 1) (byte : s.mem (State.addr p) = b)
    (low : s.gpr .r3 = BitVec.ofNat 32 (x % 2 ^ 32))
    (high : s.gpr .r4 = BitVec.ofNat 32 (exponentHigh x)) :
    WP isa exponentByte s fun t =>
      t.gpr .r3 = BitVec.ofNat 32 ((256 * x + b.toNat) % 2 ^ 32) ∧
      t.gpr .r4 = BitVec.ofNat 32 (exponentHigh (256 * x + b.toNat)) ∧
      t.gpr .r1 = p + 1 ∧ t.gpr .lr = BitVec.ofNat 32 (c - 1) ∧ t.z = decide (c = 1) ∧
      t.mem = s.mem ∧ Rest [.r1, .r3, .r4, .r5, .r7, .lr] s t := by
  rw [exponentByte, WP.seq_iff]
  refine WP.mono (exponentConsume_ok s (by rw [ptr]; simp) read byte low high) ?_
  rintro u ⟨lowU, highU, memU, restU⟩
  refine WP.mono (exponentAdvance_ok u hc hc' ((restU.gpr .lr (by simp)).trans count)) ?_
  rintro t ⟨ptrT, countT, zero, memT, restT⟩
  exact ⟨(restT.gpr .r3 (by simp)).trans lowU, (restT.gpr .r4 (by simp)).trans highU,
    by rw [ptrT, restU.gpr .r1 (by simp), ptr], countT, zero, memT.trans memU,
    (restU.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Bignum.Arm
