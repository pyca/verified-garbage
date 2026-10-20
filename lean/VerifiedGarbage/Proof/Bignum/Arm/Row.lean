module
public import VerifiedGarbage.Impl.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Bignum.Arm.RowState

import VerifiedGarbage.Proof.Bignum.Arm.RowBody2
import VerifiedGarbage.Proof.Bignum.Arm.RowBody
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Termination, memory safety and correctness of a runtime-length ARMv7 row -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Fupd mask16 wp_movw wp_mov wp_dp wp_cmp op2_lsr op2_lsl op2_reg op2_imm
  dpVal ofNat_beq_zero)

/-- The scalar's halves put back together (`rowJoin`). -/
theorem join16 (x : BitVec 32) : (x &&& mask16) ||| ((x >>> 16) <<< 16) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ones : ∀ j < 16, (0xffff : BitVec 16).getLsbD j = true := by decide
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, mask16, BitVec.getLsbD_setWidth]
  by_cases h : i < 16
  · simp only [ones i h, h, hi, decide_true, Bool.and_true, Bool.not_true,
      Bool.and_false, Bool.false_and, Bool.or_false]
  · have h16 : 16 + (i - 16) = i := by omega
    simp only [h, hi, h16, decide_true, decide_false, Bool.true_and, Bool.not_false]
    cases x.getLsbD i <;> simp only [Bool.false_and, Bool.or_false, Bool.or_true]

/-- The scalar split into its halves, and the mask, for the loop. -/
theorem rowSplit_ok (s : State) :
    WP isa (.block rowSplit) s fun t =>
      t.gpr .r1 = s.gpr .r1 &&& mask16 ∧ t.gpr .r10 = s.gpr .r1 >>> 16 ∧
      t.gpr .r9 = mask16 ∧ t.mem = s.mem ∧ Rest [.r1, .r9, .r10] s t := by
  unfold rowSplit
  refine wp_movw fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u3.gpr, dpVal, u2.other .r1 (by decide), u1.other .r1 (by decide),
      u2.other .r9 (by decide), u1.gpr]
  · rw [u3.other .r10 (by decide), u2.gpr, u1.other .r1 (by decide)]
  · rw [u3.other .r9 (by decide), u2.other .r9 (by decide), u1.gpr]
  · rw [u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))

/-- The pair loop, from the invariant after `i` words with `n - i` even and
nonzero, runs to the end of the row. -/
theorem rowLoop2_ok {s1 s : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : RowCtx s1 base size o b n) (inv : RowLoopInv s1 x base o b n i s) (hi : i < n)
    (he : (n - i) % 2 = 0)
    (h1 : s1.gpr .r1 = x &&& mask16) (h10 : s1.gpr .r10 = x >>> 16) (h9 : s1.gpr .r9 = mask16) :
    WP isa rowLoop2 s (RowLoopInv s1 x base o b n n) := by
  unfold rowLoop2
  let P := fun k t => ∃ j, j + 2 * k = n ∧ 0 < k ∧ RowLoopInv s1 x base o b n j t
  refine WP.loop (M := isa) P ?_ ((n - i) / 2) s ⟨i, by omega, by omega, inv⟩
  intro k t h
  obtain ⟨j, hjk, hk, hj⟩ := h
  refine WP.mono (rowBody2_ok ctx hj (by omega) h1 h10 h9) ?_
  rintro u ⟨hu, hz⟩
  by_cases hd : j + 2 = n
  · left
    refine ⟨?_, hd ▸ hu⟩
    change some (!u.z) = some false
    simp only [hz, hd, decide_true, Bool.not_true]
  · right
    refine ⟨?_, k - 1, by omega, j + 2, by omega, by omega, hu⟩
    change some (!u.z) = some true
    simp only [hz, hd, decide_false, Bool.not_false]

/-- The low bit of a count. -/
theorem ofNat_and_one {n : Nat} (h : n < 2 ^ 32) :
    BitVec.ofNat 32 n &&& (1 : BitVec 32) = BitVec.ofNat 32 (n % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  omega

theorem sub_zero32 (x : BitVec 32) : x - (0 : BitVec 32) = x := BitVec.sub_zero x

/-- The invariant survives changes to registers a step may change anyway
and to the flags. -/
theorem RowLoopInv.of_rest {s1 s t : State} {x base : BitVec 32} {o b n i : Nat}
    (inv : RowLoopInv s1 x base o b n i s) (hr : Rest [.r2] s t) (hm : t.mem = s.mem)
    (h11 : t.gpr .r11 = s.gpr .r11) : RowLoopInv s1 x base o b n i t :=
  ⟨inv.index, by rw [hr.gpr .r0 (by simp)]; exact inv.outPtr,
    by rw [hr.gpr .r12 (by simp)]; exact inv.inPtr, by rw [hr.gpr .lr (by simp)]; exact inv.count,
    by rw [hm]; exact inv.outside, by rw [hm, h11]; exact inv.value,
    inv.rest.trans (hr.mono (by simp [stepClobbers]))⟩

/-- A nonempty row computes the full scalar product plus the original
accumulator and carry. The final carry is kept separately, so the theorem
places no bound on the multiword inputs beyond their representation. -/
theorem row_ok (s : State) {base : BitVec 32} {size o b n : Nat}
    (ctx : RowCtx s base size o b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa row s (RowInv s base o b n n) := by
  have hn32 : n < 2 ^ 32 := by have := ctx.nowrap; have := ctx.outFits; omega
  rw [row, WP.seq_iff]
  apply WP.block_append_iff.mpr
  refine WP.mono (rowSplit_ok s) ?_
  rintro s1 ⟨h1, h10, h9, mem1, rest1⟩
  have ctx1 : RowCtx s1 base size o b n :=
    ⟨ctx.nowrap, ctx.outFits, ctx.inFits, ctx.separate, by rw [rest1.wr]; exact ctx.writable⟩
  let x := s.gpr .r1
  have init : RowLoopInv s1 x base o b n 0 s1 := by
    refine ⟨by omega, ?_, ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
    · rw [rest1.gpr .r0 (by simp)]
      simpa only [Nat.mul_zero, Nat.add_zero] using hp0
    · rw [rest1.gpr .r12 (by simp)]
      simpa only [Nat.mul_zero, Nat.add_zero] using hp12
    · rw [rest1.gpr .lr (by simp)]
      simpa only [Nat.sub_zero] using hcount
    · simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  have lr1 : s1.gpr .lr = BitVec.ofNat 32 n := (rest1.gpr .lr (by simp)).trans hcount
  -- The parity of the count.
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => wp_cmp (op2_imm (by decide)) fun s3 f3 hz3 =>
    WP.block_nil ?_
  have z3 : s3.z = decide (n % 2 = 0) := by
    rw [hz3, u2.gpr, dpVal, lr1, ofNat_and_one hn32, sub_zero32,
      ofNat_beq_zero (by omega)]
  have inv3 : RowLoopInv s1 x base o b n 0 s3 :=
    init.of_rest ((u2.rest (by simp)).trans (f3.rest _)) (by rw [f3.mem, u2.mem])
      (by rw [f3.gpr, u2.other .r11 (by decide)])
  -- An odd count takes its first word alone.
  rw [WP.seq_iff]
  refine WP.mono (Q := RowLoopInv s1 x base o b n (n % 2)) ?_ fun t ht => ?_
  · refine WP.ite (!s3.z) rfl (fun hb => ?_) (fun hb => WP.block_nil ?_)
    · have hodd : n % 2 = 0 + 1 := by
        rw [z3] at hb; simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb; omega
      refine WP.mono (rowBody_ok ctx1 inv3 (by omega) h1 h10 h9) fun u hu => ?_
      rw [hodd]
      exact hu.1
    · have heven : n % 2 = 0 := by
        rw [z3] at hb; simp only [Bool.not_eq_false', decide_eq_true_eq] at hb; exact hb
      rw [heven]
      exact inv3
  rw [WP.seq_iff]
  refine wp_cmp (op2_imm (by decide)) fun t1 f1 hz1 => WP.block_nil ?_
  have inv1 : RowLoopInv s1 x base o b n (n % 2) t1 :=
    ht.of_rest (f1.rest _) f1.mem (by rw [f1.gpr])
  have z1 : t1.z = decide (n - n % 2 = 0) := by
    rw [hz1, ht.count, sub_zero32, ofNat_beq_zero (by omega)]
  -- The rest, two words at a time.
  rw [WP.seq_iff]
  refine WP.mono (Q := RowLoopInv s1 x base o b n n) ?_ fun t ht => ?_
  · refine WP.ite (!t1.z) rfl (fun hb => ?_) (fun hb => WP.block_nil ?_)
    · rw [z1] at hb; simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb
      exact rowLoop2_ok ctx1 inv1 (by omega) (by omega) h1 h10 h9
    · rw [z1] at hb; simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
      have e : n % 2 = n := by omega
      exact cast (congrArg (fun i => RowLoopInv s1 x base o b n i t1) e) inv1
  refine wp_dp (op2_lsl (by decide)) fun u hu => WP.block_nil ?_
  have r1 : u.gpr .r1 = s.gpr .r1 := by
    rw [hu.gpr, dpVal, ht.rest.gpr .r1 (by simp), ht.rest.gpr .r10 (by simp), h1, h10]
    exact join16 _
  refine ⟨ht.index, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.other .r0 (by decide)]; exact ht.outPtr
  · rw [hu.other .r12 (by decide)]; exact ht.inPtr
  · rw [hu.other .lr (by decide)]; exact ht.count
  · rw [hu.mem, ← mem1]; exact ht.outside
  · rw [hu.mem, hu.other .r11 (by decide), ← mem1, ← rest1.gpr .r11 (by simp)]
    exact ht.value
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · by_cases e : r = .r1
      · subst e; exact r1
      · rw [hu.other r e, ht.rest.gpr r (by cases r <;> simp_all [loopClobbers]),
          rest1.gpr r (by cases r <;> simp_all [loopClobbers])]
    · rw [hu.rd, ht.rest.rd, rest1.rd]
    · rw [hu.wr, ht.rest.wr, rest1.wr]
    · rw [hu.sp, ht.rest.sp, rest1.sp]

end VG.Proof.Bignum.Arm
