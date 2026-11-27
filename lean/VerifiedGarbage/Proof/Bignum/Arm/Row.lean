module

public import VerifiedGarbage.Impl.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Bignum.Arm.RowState
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Bignum.Arm.RowBody`, which this module and modules that import it used -/

section

/-! # One iteration preserves the full row invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest mask16 ofNat_beq_zero)

theorem rowBody_ok {s0 s : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : RowCtx s0 base size o b n) (inv : RowLoopInv s0 x base o b n i s) (hi : i < n)
    (h1 : s0.gpr .r1 = x &&& mask16) (h10 : s0.gpr .r10 = x >>> 16) (h9 : s0.gpr .r9 = mask16) :
    WP isa rowBody s fun t => RowLoopInv s0 x base o b n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hn := ctx.nowrap
  have readB := row_writable ctx inv.rest.wr (d := b + 4 * i) (by omega_using [hi, hb])
  have readB' : InRegions (s.rd ++ s.wr) (off (State.addr base) (b + 4 * i)) 4 := by
    rcases readB with ⟨R, hR, hsub⟩
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  rw [rowBody, WP.seq_iff]
  refine WP.mono (rowStep_ok s _ _ x (by rw [inv.rest.gpr .r1 (by decide), h1])
    (by rw [inv.rest.gpr .r10 (by decide), h10]) (by rw [inv.rest.gpr .r9 (by decide), h9]) (row_addr ctx inv.outPtr (by omega_using [hi, ho]))
    (row_addr ctx inv.inPtr (by omega_using [hi, hb])) readB'
    (row_writable ctx inv.rest.wr (by omega_using [hi, ho]))) ?_
  rintro s1 ⟨v1, m1, k1⟩
  obtain ⟨outside, value⟩ := row_value_step ctx inv hi m1 v1
  refine WP.mono (rowAdvance_ok s1) ?_
  rintro s2 ⟨p0, p12, cnt, zero, mem, k2⟩
  have count1 : s1.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (k1.gpr .lr (by decide)).trans inv.count
  have count2 : s2.gpr .lr = BitVec.ofNat 32 (n - (i + 1)) := by
    rw [cnt, count1]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
    congr 1
  refine ⟨⟨by omega_using [hi], ?_, ?_, count2, ?_, ?_, ?_⟩, ?_⟩
  · rw [p0, k1.gpr .r0 (by decide), inv.outPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p12, k1.gpr .r12 (by decide), inv.inPtr]
    change base + BitVec.ofNat 32 (b + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [mem]; exact outside
  · rw [mem, k2.gpr .r11 (by decide)]; exact value
  · refine inv.rest.trans ((k1.mono ?_).trans (k2.mono ?_))
    all_goals decide
  · rw [zero, count1]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi]), ofNat_beq_zero (by omega_using [ho, hn])]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_using [hi]]

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.RowBody2`, which this module and modules that import it used -/

section

/-! # Two words of a row an iteration preserve the row invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest mask16 ofNat_beq_zero)

/-- The address of a word `k` bytes above a pointer into the workspace. -/
theorem row_addr_at {s0 s : State} {base : BitVec 32} {size o b n d k : Nat}
    (ctx : RowCtx s0 base size o b n) {r : Reg}
    (hr : s.gpr r = base + BitVec.ofNat 32 d) (hd : d + k < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 k) = off (State.addr base) (d + k) := by
  rw [hr, Offset.add_add]
  exact VG.Arm.addr_add (by have := ctx.nowrap; omega_using [hd, this])

theorem rowBody2_ok {s0 s : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : RowCtx s0 base size o b n) (inv : RowLoopInv s0 x base o b n i s) (hi : i + 2 ≤ n)
    (h1 : s0.gpr .r1 = x &&& mask16) (h10 : s0.gpr .r10 = x >>> 16) (h9 : s0.gpr .r9 = mask16) :
    WP isa rowBody2 s fun t => RowLoopInv s0 x base o b n (i + 2) t ∧ t.z = decide (i + 2 = n) := by
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hn := ctx.nowrap
  have read (u : State) (hu : u.wr = s0.wr) (d : Nat) (hd : d + 4 ≤ size) :
      InRegions (u.rd ++ u.wr) (off (State.addr base) d) 4 := by
    rcases row_writable ctx hu hd with ⟨R, hR, hsub⟩
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  rw [rowBody2, WP.seq_iff]
  refine WP.mono (rowStepAt_ok s 0 (by decide) _ _ x (by rw [inv.rest.gpr .r1 (by decide), h1])
    (by rw [inv.rest.gpr .r10 (by decide), h10]) (by rw [inv.rest.gpr .r9 (by decide), h9])
    (row_addr_at ctx inv.outPtr (by omega_arith)) (row_addr_at ctx inv.inPtr (by omega_arith))
    (read s inv.rest.wr _ (by omega_arith)) (row_writable ctx inv.rest.wr (by omega_arith))) ?_
  rintro s1 ⟨v1, m1, k1⟩
  obtain ⟨outside1, value1⟩ := row_value_step ctx inv (by omega_arith) m1 v1
  have wr1 : s1.wr = s0.wr := k1.wr.trans inv.rest.wr
  have p0 : s1.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i) :=
    (k1.gpr .r0 (by decide)).trans inv.outPtr
  have p12 : s1.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * i) :=
    (k1.gpr .r12 (by decide)).trans inv.inPtr
  have rest1 : Rest stepClobbers s0 s1 := inv.rest.trans (k1.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (rowStepAt_ok s1 4 (by decide) _ _ x (by rw [rest1.gpr .r1 (by decide), h1])
    (by rw [rest1.gpr .r10 (by decide), h10]) (by rw [rest1.gpr .r9 (by decide), h9])
    (row_addr_at ctx p0 (by omega_arith)) (row_addr_at ctx p12 (by omega_arith))
    (read s1 wr1 _ (by omega_arith)) (row_writable ctx wr1 (by omega_arith))) ?_
  rintro s2 ⟨v2, m2, k2⟩
  rw [show o + 4 * i + 4 = o + 4 * (i + 1) by omega_arith] at m2
  rw [show b + 4 * i + 4 = b + 4 * (i + 1) by omega_arith, show o + 4 * i + 4 = o + 4 * (i + 1) by omega_arith] at v2
  obtain ⟨outside2, value2⟩ := row_value_step_of ctx outside1 value1 (by omega_arith) m2 v2
  refine WP.mono (rowAdvance2_ok s2) ?_
  rintro s3 ⟨q0, q12, cnt, zero, mem, k3⟩
  have count2 : s2.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (k2.gpr .lr (by decide)).trans ((k1.gpr .lr (by decide)).trans inv.count)
  have sub2 : BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 2 = BitVec.ofNat 32 (n - (i + 2)) := by
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), show n - i - 2 = n - (i + 2) by omega_arith]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [q0, k2.gpr .r0 (by decide), p0]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add, show o + 4 * i + 8 = o + 4 * (i + 2) by omega_arith]
  · rw [q12, k2.gpr .r12 (by decide), p12]
    change base + BitVec.ofNat 32 (b + 4 * i) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add, show b + 4 * i + 8 = b + 4 * (i + 2) by omega_arith]
  · rw [cnt, count2]
    exact sub2
  · rw [mem, show 4 * (i + 2) = 4 * (i + 1 + 1) by omega_arith]; exact outside2
  · rw [mem, k3.gpr .r11 (by decide), show i + 2 = i + 1 + 1 by omega_arith]; exact value2
  · refine rest1.trans ((k2.mono ?_).trans (k3.mono ?_))
    all_goals decide
  · rw [zero, count2]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 2 == 0) = _
    rw [sub2, ofNat_beq_zero (by omega_arith)]
    simp only [show n - (i + 2) = 0 ↔ i + 2 = n by omega_arith]

end VG.Proof.Bignum.Arm

end

end

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
  · have h16 : 16 + (i - 16) = i := by omega_using [h]
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
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))

/-- The pair loop, from the invariant after `i` words with `n - i` even and
nonzero, runs to the end of the row. -/
theorem rowLoop2_ok {s1 s : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : RowCtx s1 base size o b n) (inv : RowLoopInv s1 x base o b n i s) (hi : i < n)
    (he : (n - i) % 2 = 0)
    (h1 : s1.gpr .r1 = x &&& mask16) (h10 : s1.gpr .r10 = x >>> 16) (h9 : s1.gpr .r9 = mask16) :
    WP isa rowLoop2 s (RowLoopInv s1 x base o b n n) := by
  unfold rowLoop2
  let P := fun k t => ∃ j, j + 2 * k = n ∧ 0 < k ∧ RowLoopInv s1 x base o b n j t
  refine WP.loop (M := isa) P ?_ ((n - i) / 2) s ⟨i, by omega_using [hi, he], by omega_using [hi, he], inv⟩
  intro k t h
  obtain ⟨j, hjk, hk, hj⟩ := h
  refine WP.mono (rowBody2_ok ctx hj (by omega_using [hjk, hk]) h1 h10 h9) ?_
  rintro u ⟨hu, hz⟩
  by_cases hd : j + 2 = n
  · left
    refine ⟨?_, hd ▸ hu⟩
    change some (!u.z) = some false
    simp only [hz, hd, decide_true, Bool.not_true]
  · right
    refine ⟨?_, k - 1, by omega_using [hk], j + 2, by omega_using [hjk, hk], by omega_using [hjk, hk, hd], hu⟩
    change some (!u.z) = some true
    simp only [hz, hd, decide_false, Bool.not_false]

/-- The low bit of a count. -/
theorem ofNat_and_one {n : Nat} (h : n < 2 ^ 32) :
    BitVec.ofNat 32 n &&& (1 : BitVec 32) = BitVec.ofNat 32 (n % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  omega_using []

theorem sub_zero32 (x : BitVec 32) : x - (0 : BitVec 32) = x := BitVec.sub_zero x

/-- The invariant survives changes to registers a step may change anyway
and to the flags. -/
theorem RowLoopInv.of_rest {s1 s t : State} {x base : BitVec 32} {o b n i : Nat}
    (inv : RowLoopInv s1 x base o b n i s) (hr : Rest [.r2] s t) (hm : t.mem = s.mem)
    (h11 : t.gpr .r11 = s.gpr .r11) : RowLoopInv s1 x base o b n i t :=
  ⟨inv.index, by rw [hr.gpr .r0 (by decide)]; exact inv.outPtr,
    by rw [hr.gpr .r12 (by decide)]; exact inv.inPtr, by rw [hr.gpr .lr (by decide)]; exact inv.count,
    by rw [hm]; exact inv.outside, by rw [hm, h11]; exact inv.value,
    inv.rest.trans (hr.mono (by decide))⟩

/-- A nonempty row computes the full scalar product plus the original
accumulator and carry. The final carry is kept separately, so the theorem
places no bound on the multiword inputs beyond their representation. -/
theorem row_ok (s : State) {base : BitVec 32} {size o b n : Nat}
    (ctx : RowCtx s base size o b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa row s (RowInv s base o b n n) := by
  have hn32 : n < 2 ^ 32 := by have := ctx.nowrap; have := ctx.outFits; omega_arith
  rw [row, WP.seq_iff]
  apply WP.block_append_iff.mpr
  refine WP.mono (rowSplit_ok s) ?_
  rintro s1 ⟨h1, h10, h9, mem1, rest1⟩
  have ctx1 : RowCtx s1 base size o b n :=
    ⟨ctx.nowrap, ctx.outFits, ctx.inFits, ctx.separate, by rw [rest1.wr]; exact ctx.writable⟩
  let x := s.gpr .r1
  have init : RowLoopInv s1 x base o b n 0 s1 := by
    refine ⟨by omega_using [], ?_, ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
    · rw [rest1.gpr .r0 (by decide)]
      simpa only [Nat.mul_zero, Nat.add_zero] using hp0
    · rw [rest1.gpr .r12 (by decide)]
      simpa only [Nat.mul_zero, Nat.add_zero] using hp12
    · rw [rest1.gpr .lr (by decide)]
      simpa only [Nat.sub_zero] using hcount
    · simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  have lr1 : s1.gpr .lr = BitVec.ofNat 32 n := (rest1.gpr .lr (by decide)).trans hcount
  -- The parity of the count.
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => wp_cmp (op2_imm (by decide)) fun s3 f3 hz3 =>
    WP.block_nil ?_
  have z3 : s3.z = decide (n % 2 = 0) := by
    rw [hz3, u2.gpr, dpVal, lr1, ofNat_and_one hn32, sub_zero32,
      ofNat_beq_zero (by omega_using [])]
  have inv3 : RowLoopInv s1 x base o b n 0 s3 :=
    init.of_rest ((u2.rest (by decide)).trans (f3.rest _)) (by rw [f3.mem, u2.mem])
      (by rw [f3.gpr, u2.other .r11 (by decide)])
  -- An odd count takes its first word alone.
  rw [WP.seq_iff]
  refine WP.mono (Q := RowLoopInv s1 x base o b n (n % 2)) ?_ fun t ht => ?_
  · refine WP.ite (!s3.z) rfl (fun hb => ?_) (fun hb => WP.block_nil ?_)
    · have hodd : n % 2 = 0 + 1 := by
        rw [z3] at hb; simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb; omega_using [hb]
      refine WP.mono (rowBody_ok ctx1 inv3 (by omega_using [hn]) h1 h10 h9) fun u hu => ?_
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
    rw [hz1, ht.count, sub_zero32, ofNat_beq_zero (by omega_using [hn32])]
  -- The rest, two words at a time.
  rw [WP.seq_iff]
  refine WP.mono (Q := RowLoopInv s1 x base o b n n) ?_ fun t ht => ?_
  · refine WP.ite (!t1.z) rfl (fun hb => ?_) (fun hb => WP.block_nil ?_)
    · rw [z1] at hb; simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb
      exact rowLoop2_ok ctx1 inv1 (by omega_using [hb]) (by omega_using []) h1 h10 h9
    · rw [z1] at hb; simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
      have e : n % 2 = n := by omega_using [hb]
      exact cast (congrArg (fun i => RowLoopInv s1 x base o b n i t1) e) inv1
  refine wp_dp (op2_lsl (by decide)) fun u hu => WP.block_nil ?_
  have r1 : u.gpr .r1 = s.gpr .r1 := by
    rw [hu.gpr, dpVal, ht.rest.gpr .r1 (by decide), ht.rest.gpr .r10 (by decide), h1, h10]
    exact join16 _
  refine ⟨ht.index, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.other .r0 (by decide)]; exact ht.outPtr
  · rw [hu.other .r12 (by decide)]; exact ht.inPtr
  · rw [hu.other .lr (by decide)]; exact ht.count
  · rw [hu.mem, ← mem1]; exact ht.outside
  · rw [hu.mem, hu.other .r11 (by decide), ← mem1, ← rest1.gpr .r11 (by decide)]
    exact ht.value
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · by_cases e : r = .r1
      · subst e; exact r1
      · rw [hu.other r e, ht.rest.gpr r (by revert hr e; cases r <;> decide),
          rest1.gpr r (by revert hr e; cases r <;> decide)]
    · rw [hu.rd, ht.rest.rd, rest1.rd]
    · rw [hu.wr, ht.rest.wr, rest1.wr]
    · rw [hu.sp, ht.rest.sp, rest1.sp]

end VG.Proof.Bignum.Arm
