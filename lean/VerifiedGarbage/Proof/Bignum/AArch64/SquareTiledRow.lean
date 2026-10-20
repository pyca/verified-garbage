module
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.Row

import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRow

/-! Four-word rows with exact scalar-tail handling. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)

theorem blocks_guard_ok {s₀ t : State} {B : Addr} {Z w eA eb q : Nat}
    (h7 : s₀.gpr .x7 = 0) (hA : eA + 8*w ≤ Z) (hb : eb + 8*w ≤ Z)
    (hsep : eA + 8*w ≤ eb ∨ eb + 8*w ≤ eA)
    (hq64 : q < 2 ^ 64) (hqn : 4*q ≤ w)
    (h0 : RowInv s₀ B Z eA eb 0 t) (h14 : t.gpr .x14 = BitVec.ofNat 64 q) :
    WP isa (.ite (.nonzero .x .x14)
      (countLoop .x14 VG.Impl.Bignum.AArch64.Square.mac4) (.block [])) t
      (RowInv s₀ B Z eA eb (4*q)) := by
  by_cases hq : q = 0
  · subst q
    refine WP.ite false (by rw [eval_nonzero, h14]; rfl) (by simp)
      (fun _ => WP.block_nil ?_)
    simpa only [Nat.mul_zero] using h0
  · refine WP.ite true ?_ (fun _ => blocks4_ok h7 hA hb hsep (by omega) hq64 hqn h0 h14) (by simp)
    rw [eval_nonzero, h14, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq64]
    rw [decide_eq_true hq]

theorem remainder_guard_ok {s₀ t : State} {B : Addr} {Z w eA eb j r : Nat}
    (h7 : s₀.gpr .x7 = 0) (hA : eA + 8*w ≤ Z) (hb : eb + 8*w ≤ Z)
    (hsep : eA + 8*w ≤ eb ∨ eb + 8*w ≤ eA)
    (hr64 : r < 2 ^ 64) (hjr : j+r ≤ w)
    (h0 : RowInv s₀ B Z eA eb j t) (h14 : t.gpr .x14 = BitVec.ofNat 64 r) :
    WP isa (.ite (.nonzero .x .x14) (countLoop .x14 (mac false)) (.block [])) t
      (RowInv s₀ B Z eA eb (j+r)) := by
  by_cases hr : r = 0
  · subst r
    refine WP.ite false (by rw [eval_nonzero, h14]; rfl) (by simp)
      (fun _ => WP.block_nil ?_)
    simpa only [Nat.add_zero] using h0
  · refine WP.ite true ?_ (fun _ => remainder_ok h7 hA hb hsep (by omega) hr64 hjr h0 h14) (by simp)
    rw [eval_nonzero, h14, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr64]
    rw [decide_eq_true hr]

/-- Both full blocks and tails implement the existing row invariant. -/
theorem tiledRow_ok {s₀ s : State} {B : Addr} {Z n eA eb : Nat} {count : Reg}
    (h7 : s₀.gpr .x7 = 0) (hA : eA + 8*n ≤ Z) (hb : eb + 8*n ≤ Z)
    (hsep : eA + 8*n ≤ eb ∨ eb + 8*n ≤ eA)
    (hn : n < 2 ^ 64) (hC : count = .x12 ∨ count = .x13)
    (hcount : s.gpr count = BitVec.ofNat 64 n) (h0 : RowInv s₀ B Z eA eb 0 s) :
    WP isa (VG.Impl.Bignum.AArch64.Square.tiledRow count) s
      (RowInv s₀ B Z eA eb n) := by
  have hkeep : count ∉ [.x2, .x3, .x4, .x14, .x16, .x17] := by
    rcases hC with rfl | rfl <;> decide
  unfold VG.Impl.Bignum.AArch64.Square.tiledRow
  refine WP.seq (WP.mono (shift_count_ok s count hcount hn) fun t ⟨⟨hm, hc, h14⟩, k⟩ => ?_)
  have hI := rowInv_counter h0 hm hc (k.mono (by decide))
  refine WP.seq (WP.mono (blocks_guard_ok h7 hA hb hsep (by omega) (by omega) hI h14)
    fun u hu => ?_)
  have ucount := (hu.keep.gpr count hkeep).trans (h0.keep.gpr count hkeep).symm
  have un : u.gpr count = BitVec.ofNat 64 n := ucount.trans hcount
  refine WP.seq (WP.mono (mask_count_ok u count un hn hC) fun v ⟨⟨hmv, hcv, hv14⟩, kv⟩ => ?_)
  have hv := rowInv_counter hu hmv hcv kv
  have heq : 4*(n/4) + n%4 = n := by omega
  simpa only [heq] using (remainder_guard_ok h7 hA hb hsep (by omega) (by omega) hv hv14)

end VG.Proof.Bignum.AArch64.Square
