module
public import VerifiedGarbage.Proof.X448.Arm.RowMem
import VerifiedGarbage.Proof.X448.Arm.RowPass
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `X448.Arm.RowF`, which only this module used -/

section

/-!
# X448 on ARMv7: one row of the field functions' multiplication

The carries keep each multiply-add within a 32-bit word.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem rowHalfF_ok {x y : Nat} (hx : x + 112 ≤ ACC) (hy : y + 112 ≤ ACC) {s0 : State}
    (hlx : Bounded s0.mem (State.addr b) x) (hly : Bounded s0.mem (State.addr b) y) {i q : Nat} (hi : i < 28)
    (hq : q ≤ 1) {s : State} (h : RowInvF b x y s0 i q s) :
    WP isa (.block (rowHalfF q)) s (RowInvF b x y s0 (i + 1) (q + 1)) := by
  have hA := ACC_eq
  have hfit := h.ctx.fit
  have hqi := h.le
  have hframe0 : ∀ z : Nat, z + 112 ≤ ACC → ∀ k < 28,
      limbs s.mem (State.addr b) z k = limbs s0.mem (State.addr b) z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [rowHalfF, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * i)) (by omega_arith)
    (by rw [h.lr, eaB hfit (by omega_arith), show x + 4 * (i - q) + 4 * q = x + 4 * i by omega_arith])
    (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have hr2 : Rest [.r1, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have e12 : s2.gpr .r12 = b + BitVec.ofNat 32 y := by rw [hr2.gpr _ (by decide), h.r12]
  have hc2 : RowCtx b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e1 : (s2.gpr .r1).toNat = limbs s0.mem (State.addr b) x i := by
    rw [u2.other _ (by decide), u1.gpr, ← hframe0 x hx i hi]
  have e7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * (i - q)) := by rw [hr2.gpr _ (by decide), h.r7]
  have P7 : State.addr (s2.gpr .r7) = State.addr b + BitVec.ofNat 64 (4 * (i - q)) := by
    rw [e7]; exact addr7 hfit (by omega_arith)
  have hlt : ∀ j < 28, Radix16.rowC (accw s.mem (State.addr b)) (limbs s0.mem (State.addr b) x)
      (limbs s0.mem (State.addr b) y) i j + 65536 ≤ 2 ^ 32 := fun j hj =>
    VG.Proof.X25519.Arm.rowC_le (hlx i hi) (hly j hj) (h.lt (i + j) (by omega_arith))
  refine WP.append (carryPassT_ok (t := .r2) (rb := .r7) (o := ACC + 4 * q) (s0 := s2)
    (c := Radix16.rowC (accw s.mem (State.addr b)) (limbs s0.mem (State.addr b) x) (limbs s0.mem (State.addr b) y) i)
    (cin := 0) (.inl rfl) (by decide) (by omega_arith) (by rw [e7, toNat7 hfit (by omega_arith)]; omega_arith)
    (fun k hk => by rw [P7, Offset.add_add]; exact hc2.inW (by omega_arith))
    (by rw [hr2.gpr _ (by decide), h.r6]) (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : RowCtx b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [P7, Offset.add_add, show 4 * (i - q) + (ACC + 4 * q) = 4 * i + ACC by omega_arith] at this
    change WP isa (.block [.ldr .r2 .r12 (4 * k), .mul .r2 .r1 .r2,
      .ldr .r3 .r7 (ACC + 4 * q + 4 * k), .dp .add .r3 .r3 (.reg .r2)]) s' _
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (y + 4 * k)) (by omega_arith)
      (by rw [hp'.rest.gpr _ (by decide), e12, eaB hfit (by omega_arith)]) (hc'.inR (by omega_arith))
      fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by omega_arith)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e7,
        ea7 hfit (by omega_arith), show 4 * (i - q) + (ACC + 4 * q + 4 * k) = 4 * i + (ACC + 4 * k) by omega_arith]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega_arith))
      fun t3 v3 => ?_
    refine wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r2).toNat = limbs s0.mem (State.addr b) y k := by
        rw [v1.gpr, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      have ea : (t1.gpr .r1).toNat = limbs s0.mem (State.addr b) x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      have hab := Nat.mul_le_mul (Nat.le_of_lt_succ (hlx i hi)) (Nat.le_of_lt_succ (hly k hk))
      have e2 : (t2.gpr .r2).toNat = limbs s0.mem (State.addr b) x i * limbs s0.mem (State.addr b) y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; omega_arith), ea, ey]
      have e3 : (t3.gpr .r3).toNat = accw s.mem (State.addr b) (i + k) := by
        rw [v3.gpr, v2.mem, v1.mem, accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)]
        congr 1; omega_arith
      have := hlt k hk
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r2 (by decide), toNat_add_lt (by rw [e3, e2]; simp only [Radix16.rowC] at this; omega_arith), e3, e2,
        Radix16.rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry.
    have hc3 : RowCtx b s3 := hc2.of_rest hp.rest (by decide)
    have e7' : s3.gpr .r7 = b + BitVec.ofNat 32 (4 * (i - q)) := by rw [hp.rest.gpr _ (by decide), e7]
    refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 112))) (by omega_arith)
      (by rw [e7', ea7 hfit (by omega_arith), show 4 * (i - q) + (ACC + 4 * q + 112) = 4 * i + (ACC + 112) by omega_arith])
      (hc3.inW (by omega_arith)) fun s4 u4 => WP.block_nil ?_
    have hr6 : Rest (.lr :: fclob) s s4 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans (u4.rest _))
    have hm6 : s4.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 112))) (s3.gpr .r5) :=
      u4.mem
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 112⟩] s.mem s3.mem := by
      have := hp.frame
      rw [P7, Offset.add_add, show 4 * (i - q) + (ACC + 4 * q) = 4 * i + ACC by omega_arith] at this
      rw [← hm2]; exact this
    -- The limbs of `ACC` after the row.
    have hacc : ∀ k < i + 29, accw s4.mem (State.addr b) k =
        Radix16.rowAcc (accw s.mem (State.addr b)) (limbs s0.mem (State.addr b) x) (limbs s0.mem (State.addr b) y) i k := by
      intro k hk
      rw [accw, hm6]
      rcases Nat.lt_or_ge k (i + 28) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]
          simp only [Radix16.rowAcc, hki, ite_true]
        · have := hp.outs (k - i) (by omega_arith)
          rw [P7, wd_shift, show 4 * (i - q) + (ACC + 4 * q + 4 * (k - i)) = ACC + 4 * k by omega_arith] at this
          rw [this, out_zero]
          simp only [Radix16.rowAcc, show ¬ k < i by omega_arith, hk', ite_false, ite_true]
      · rw [show ACC + 4 * k = 4 * i + (ACC + 112) by omega_arith, wd_write_self, hp.r5, chain_zero]
        simp only [Radix16.rowAcc, show ¬ k < i by omega_arith, show ¬ k < i + 28 by omega_arith, ite_false]
    have sub1 : i + 1 - (q + 1) = i - q := by omega_arith
    refine ⟨by omega_arith, hc3.of_rest (u4.rest []) (by decide), h.rest.trans hr6,
      by rw [hr6.gpr _ (by decide), h.r6], ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_⟩
    · rw [sub1, u4.gpr, e7']
    · rw [sub1, u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.lr]
    · rw [sub1, u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.r4]
    · rw [hr6.gpr _ (by decide), h.r12]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [hacc k hk]
      exact Radix16.rowAcc_lt (fun k hk => h.lt k (by omega_arith)) (fun j hj => by have := hlt j hj; change _ ≤ 2 ^ 32 - 65536; omega_arith) k hk
    · rw [Radix16.valN_congr hacc]; exact Radix16.row_val h.val

/-- A pair of rows: `r7` and `lr` move up two words, and the count of pairs down. -/
theorem rowF_ok {x y : Nat} (hx : x + 112 ≤ ACC) (hy : y + 112 ≤ ACC) {s0 : State}
    (hlx : Bounded s0.mem (State.addr b) x) (hly : Bounded s0.mem (State.addr b) y) {i : Nat} (hi : i + 2 ≤ 28)
    {s : State} (h : RowInvF b x y s0 i 0 s) :
    WP isa (.block rowF) s fun s' =>
      RowInvF b x y s0 (i + 2) 0 s' ∧ s'.z = decide (14 - (i + 2) / 2 = 0) := by
  rw [rowF, List.append_assoc, WP.block_append_iff]
  refine WP.mono (rowHalfF_ok hx hy hlx hly (by omega_arith) (by decide) h) fun s1 h1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowHalfF_ok hx hy hlx hly (by omega_arith) (by decide) h1) fun s2 h2 => ?_
  have hfit := h2.ctx.fit
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_subs (op2_imm (by decide)) fun s5 u5 hz => WP.block_nil ?_
  have hr5 : Rest (.lr :: fclob) s2 s5 := (u3.rest (by decide)).trans ((u4.rest (by decide)).trans
    (u5.rest (by decide)))
  have hr4 : s5.gpr .r4 = BitVec.ofNat 32 (14 - (i + 2 - 0) / 2) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), h2.r4]
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sub_le (by rw [toNat_imm (by omega_arith), t1]; omega_arith), toNat_imm (by omega_arith), toNat_imm (by omega_arith),
      t1]
    omega_arith
  have m5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  refine ⟨⟨by omega_arith, h2.ctx.of_rest hr5 (by decide), h2.rest.trans hr5, by rw [hr5.gpr _ (by decide), h2.r6],
    ?_, ?_, hr4, by rw [hr5.gpr _ (by decide), h2.r12], m5 ▸ h2.frame, m5 ▸ h2.lt, m5 ▸ h2.val⟩, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, h2.r7]
    show b + BitVec.ofNat 32 (4 * (i + 1 + 1 - (0 + 1 + 1))) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add, show 4 * (i + 1 + 1 - (0 + 1 + 1)) + 8 = 4 * (i + 2 - 0) by omega_arith]
  · rw [u5.other _ (by decide), u4.gpr, u3.other _ (by decide), h2.lr]
    show b + BitVec.ofNat 32 (x + 4 * (i + 1 + 1 - (0 + 1 + 1))) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add, show x + 4 * (i + 1 + 1 - (0 + 1 + 1)) + 8 = x + 4 * (i + 2 - 0) by omega_arith]
  · rw [hz, ← u5.gpr, hr4, ofNat_beq_zero (by omega_arith), Nat.sub_zero]

end VG.Proof.X448.Arm

end

end

/-! ### `X448.Arm.Row`, which only this module used -/

section

/-!
# X448 on ARMv7: one row of multiplication

The carries keep each multiply-add within a 32-bit word.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem row_ok {x y : Nat} (hx : x + 112 ≤ ACC) (hy : y + 112 ≤ ACC) {s0 : State}
    (hlx : Bounded s0.mem (State.addr b) x) (hly : Bounded s0.mem (State.addr b) y) {i : Nat} (hi : i < 28)
    {s : State} (h : RowInv b x y s0 i s) :
    WP isa (.block (row x y)) s fun s' =>
      RowInv b x y s0 (i + 1) s' ∧ s'.z = decide (28 - (i + 1) = 0) := by
  have hA := ACC_eq
  have hfit := h.ctx.fit
  have hframe0 : ∀ z : Nat, z + 112 ≤ ACC → ∀ k < 28,
      limbs s.mem (State.addr b) z k = limbs s0.mem (State.addr b) z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [row, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * i)) (by omega_arith)
    (by rw [h.r7, ea7 hfit (by omega_arith), Nat.add_comm]) (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have hr2 : Rest [.r1, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : RowCtx b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e1 : (s2.gpr .r1).toNat = limbs s0.mem (State.addr b) x i := by
    rw [u2.other _ (by decide), u1.gpr, ← hframe0 x hx i hi]
  have e7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hr2.gpr _ (by decide), h.r7]
  have P7 : State.addr (s2.gpr .r7) = State.addr b + BitVec.ofNat 64 (4 * i) := by
    rw [e7]; exact addr7 hfit (by omega_arith)
  have hlt : ∀ j < 28, Radix16.rowC (accw s.mem (State.addr b)) (limbs s0.mem (State.addr b) x)
      (limbs s0.mem (State.addr b) y) i j + 65536 ≤ 2 ^ 32 := fun j hj =>
    VG.Proof.X25519.Arm.rowC_le (hlx i hi) (hly j hj) (h.lt (i + j) (by omega_arith))
  refine WP.append (carryPass_ok (rb := .r7) (o := ACC) (s0 := s2)
    (c := Radix16.rowC (accw s.mem (State.addr b)) (limbs s0.mem (State.addr b) x) (limbs s0.mem (State.addr b) y) i)
    (cin := 0) (by decide) (by omega_arith) (by rw [e7, toNat7 hfit (by omega_arith)]; omega_arith)
    (fun k hk => by rw [P7, Offset.add_add]; exact hc2.inW (by omega_arith))
    (by rw [hr2.gpr _ (by decide), h.r6]) (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : RowCtx b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [P7, Offset.add_add] at this
    change WP isa (.block [ld .r2 (y + 4 * k), .mul .r2 .r1 .r2,
      .ldr .r3 .r7 (ACC + 4 * k), .dp .add .r3 .r3 (.reg .r2)]) s' _
    refine rowLoad_ok hc' (d := y + 4 * k) (by omega_arith) fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by omega_arith)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e7,
        ea7 hfit (by omega_arith)]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega_arith))
      fun t3 v3 => ?_
    refine wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r2).toNat = limbs s0.mem (State.addr b) y k := by
        rw [v1.gpr, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      have ea : (t1.gpr .r1).toNat = limbs s0.mem (State.addr b) x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      have hab := Nat.mul_le_mul (Nat.le_of_lt_succ (hlx i hi)) (Nat.le_of_lt_succ (hly k hk))
      have e2 : (t2.gpr .r2).toNat = limbs s0.mem (State.addr b) x i * limbs s0.mem (State.addr b) y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; omega_arith), ea, ey]
      have e3 : (t3.gpr .r3).toNat = accw s.mem (State.addr b) (i + k) := by
        rw [v3.gpr, v2.mem, v1.mem, accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)]
        congr 1; omega_arith
      have := hlt k hk
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r2 (by decide), toNat_add_lt (by rw [e3, e2]; simp only [Radix16.rowC] at this; omega_arith), e3, e2,
        Radix16.rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    have hc3 : RowCtx b s3 := hc2.of_rest hp.rest (by decide)
    have e7' : s3.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hp.rest.gpr _ (by decide), e7]
    refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 112))) (by omega_arith)
      (by rw [e7', ea7 hfit (by omega_arith)]) (hc3.inW (by omega_arith)) fun s4 u4 => ?_
    refine wp_dp (op2_imm (by decide)) fun s5 u5 => wp_subs (op2_imm (by decide)) fun s6 u6 hz => ?_
    refine WP.block_nil ?_
    have hr6 : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans (u6.rest (by decide)))))
    have hm6 : s6.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 112))) (s3.gpr .r5) := by
      rw [u6.mem, u5.mem, u4.mem]
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 112⟩] s.mem s3.mem := by
      have := hp.frame; rw [P7, Offset.add_add] at this; rw [← hm2]; exact this
    have hr9 : s6.gpr .r9 = BitVec.ofNat 32 (28 - (i + 1)) := by
      rw [u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.r9]
      have t1 : (1 : BitVec 32).toNat = 1 := rfl
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sub_le (by rw [toNat_imm (by omega_arith), t1]; omega_arith), toNat_imm (by omega_arith), toNat_imm (by omega_arith),
        t1]
      omega_arith
    -- The limbs of `ACC` after the row.
    have hacc : ∀ k < i + 29, accw s6.mem (State.addr b) k =
        Radix16.rowAcc (accw s.mem (State.addr b)) (limbs s0.mem (State.addr b) x) (limbs s0.mem (State.addr b) y) i k := by
      intro k hk
      rw [accw, hm6]
      rcases Nat.lt_or_ge k (i + 28) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]
          simp only [Radix16.rowAcc, hki, ite_true]
        · have := hp.outs (k - i) (by omega_arith)
          rw [P7, wd_shift, show 4 * i + (ACC + 4 * (k - i)) = ACC + 4 * k by omega_arith] at this
          rw [this, out_zero]
          simp only [Radix16.rowAcc, show ¬ k < i by omega_arith, hk', ite_false, ite_true]
      · rw [show ACC + 4 * k = 4 * i + (ACC + 112) by omega_arith, wd_write_self, hp.r5, chain_zero]
        simp only [Radix16.rowAcc, show ¬ k < i by omega_arith, show ¬ k < i + 28 by omega_arith, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r7, .r9]).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
        (by decide), h.rest.trans (hr6.mono (by decide)), by rw [hr6.gpr _ (by decide), h.r6],
      ?_, hr9, ?_, fun k hk => ?_, ?_⟩, ?_⟩
    · rw [u6.other _ (by decide), u5.gpr, u4.gpr, e7']
      show b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
      rw [Offset.add_add, Nat.mul_succ]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [hacc k hk]
      exact Radix16.rowAcc_lt (fun k hk => h.lt k (by omega_arith)) (fun j hj => by have := hlt j hj; change _ ≤ 2 ^ 32 - 65536; omega_arith) k hk
    · rw [Radix16.valN_congr hacc]; exact Radix16.row_val h.val
    · rw [hz, ← u6.gpr, hr9, ofNat_beq_zero (by omega_arith)]

end VG.Proof.X448.Arm

end

end


/-!
# X448 on ARMv7: the multiplication loop

All 28 rows terminate at a public counter, producing 56 bounded product limbs.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

theorem mulLoop_ok {b : BitVec 32} {x y : Nat} (hx : Slot x) (hy : Slot y)
    {s0 s : State} (hlx : Bounded s0.mem (State.addr b) x) (hly : Bounded s0.mem (State.addr b) y)
    (hs : RowInv b x y s0 0 s) :
    WP isa (.loop (.block (row x y)) .ne) s (RowInv b x y s0 28) := by
  refine WP.loop (M := isa)
    (fun n s' => ∃ i, n = 28 - i ∧ i < 28 ∧ RowInv b x y s0 i s') ?_ 28 s ⟨0, rfl, by decide, hs⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (row_ok hx hy hlx hly hi hr) fun t ⟨ht, hz⟩ => ?_
  by_cases h28 : i + 1 = 28
  · refine .inl ⟨by rw [eval_ne, hz]; simp only [h28, decide_true, Bool.not_true], ?_⟩
    rw [h28] at ht
    exact ht
  · exact .inr ⟨by rw [eval_ne, hz]; simp; omega_using [hi, h28],
      28 - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, h28], ht⟩

theorem mulLoopF_ok {b : BitVec 32} {x y : Nat} (hx : Slot x) (hy : Slot y)
    {s0 s : State} (hlx : Bounded s0.mem (State.addr b) x) (hly : Bounded s0.mem (State.addr b) y)
    (hs : RowInvF b x y s0 0 0 s) :
    WP isa (.loop (.block rowF) .ne) s (RowInvF b x y s0 28 0) := by
  refine WP.loop (M := isa)
    (fun n s' => ∃ m, n = 14 - m ∧ m < 14 ∧ RowInvF b x y s0 (2 * m) 0 s') ?_ 14 s ⟨0, rfl, by decide, hs⟩
  rintro n s' ⟨m, rfl, hm, hr⟩
  refine WP.mono (rowF_ok hx hy hlx hly (by omega_using [hm]) hr) fun t ⟨ht, hz⟩ => ?_
  rw [show 2 * m + 2 = 2 * (m + 1) by omega_using []] at ht hz
  by_cases h14 : m + 1 = 14
  · refine .inl ⟨by rw [eval_ne, hz]; simp only [h14]; decide, ?_⟩
    rw [h14] at ht
    exact ht
  · exact .inr ⟨by rw [eval_ne, hz]; simp; omega_using [hm, h14],
      14 - (m + 1), by omega_using [hm], m + 1, rfl, by omega_using [hm, h14], ht⟩

end VG.Proof.X448.Arm
