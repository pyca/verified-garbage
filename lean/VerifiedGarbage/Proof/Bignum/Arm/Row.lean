module

public import VerifiedGarbage.Proof.Bignum.Arm.RowBody

/-! # Termination, memory safety and correctness of a runtime-length ARMv7 row -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd mask16 wp_movw wp_mov wp_dp op2_lsr op2_lsl op2_reg dpVal)

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

/-- A nonempty row computes the full scalar product plus the original
accumulator and carry. The final carry is kept separately, so the theorem
places no bound on the multiword inputs beyond their representation. -/
theorem row_ok (s : State) {base : BitVec 32} {size o b n : Nat}
    (ctx : RowCtx s base size o b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa row s (RowInv s base o b n n) := by
  rw [row, WP.seq_iff]
  refine WP.mono (rowSplit_ok s) ?_
  rintro s1 ⟨h1, h10, h9, mem1, rest1⟩
  have ctx1 : RowCtx s1 base size o b n :=
    ⟨ctx.nowrap, ctx.outFits, ctx.inFits, ctx.separate, by rw [rest1.wr]; exact ctx.writable⟩
  rw [WP.seq_iff]
  let x := s.gpr .r1
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ RowLoopInv s1 x base o b n i t
  have loop : WP isa rowLoop s1 (RowLoopInv s1 x base o b n n) := by
    unfold rowLoop
    refine WP.loop (M := isa) inv ?_ n s1 ?_
    · intro k t h
      obtain ⟨i, hik, hk, hi⟩ := h
      refine WP.mono (rowBody_ok ctx1 hi (by omega) h1 h10 h9) ?_
      rintro u ⟨hu, hz⟩
      by_cases he : i + 1 = n
      · left
        refine ⟨?_, he ▸ hu⟩
        change some (!u.z) = some false
        simp only [hz, he, decide_true, Bool.not_true]
      · right
        refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
        change some (!u.z) = some true
        simp only [hz, he, decide_false, Bool.not_false]
    · refine ⟨0, by omega, hn, ?_⟩
      refine ⟨by omega, ?_, ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
      · rw [rest1.gpr .r0 (by simp)]
        simpa only [Nat.mul_zero, Nat.add_zero] using hp0
      · rw [rest1.gpr .r12 (by simp)]
        simpa only [Nat.mul_zero, Nat.add_zero] using hp12
      · rw [rest1.gpr .lr (by simp)]
        simpa only [Nat.sub_zero] using hcount
      · simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  refine WP.mono loop ?_
  intro t ht
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
