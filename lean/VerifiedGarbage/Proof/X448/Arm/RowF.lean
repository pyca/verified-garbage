import VerifiedGarbage.Proof.X448.Arm.Row

/-!
# X448 on ARMv7: one row of the field functions' multiplication

The carries keep each multiply-add within a 32-bit word.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

theorem sub_beq_zero {a c : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 c == 0) = decide (a = c) := by
  by_cases h : a = c
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at this
    change _ = 0 at this
    omega

variable {b : BitVec 32}

theorem rowF_ok {x y : Nat} (hx : x + 112 ≤ ACC) (hy : y + 112 ≤ ACC) {s0 : State}
    (hlx : Bounded s0.mem (State.addr b) x) (hly : Bounded s0.mem (State.addr b) y) {i : Nat} (hi : i < 28)
    {s : State} (h : RowInvF b x y s0 i s) :
    WP isa (.block rowF) s fun s' =>
      RowInvF b x y s0 (i + 1) s' ∧ s'.z = decide (28 - (i + 1) = 0) := by
  have hA := ACC_eq
  have hfit := h.ctx.fit
  have hframe0 : ∀ z : Nat, z + 112 ≤ ACC → ∀ k < 28,
      limbs s.mem (State.addr b) z k = limbs s0.mem (State.addr b) z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  simp only [rowF, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * i)) (by omega)
    (by rw [h.lr, eaB hfit (by omega), Nat.add_zero]) (h.ctx.inR (by omega)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have hr2 : Rest [.r1, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have e12 : s2.gpr .r12 = b + BitVec.ofNat 32 y := by rw [hr2.gpr _ (by decide), h.r12]
  have hc2 : RowCtx b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e1 : (s2.gpr .r1).toNat = limbs s0.mem (State.addr b) x i := by
    rw [u2.other _ (by decide), u1.gpr, ← hframe0 x hx i hi]
  have e7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hr2.gpr _ (by decide), h.r7]
  have P7 : State.addr (s2.gpr .r7) = State.addr b + BitVec.ofNat 64 (4 * i) := by
    rw [e7]; exact addr7 hfit (by omega)
  have hlt : ∀ j < 28, Radix16.rowC (accw s.mem (State.addr b)) (limbs s0.mem (State.addr b) x)
      (limbs s0.mem (State.addr b) y) i j + 65536 ≤ 2 ^ 32 := fun j hj =>
    VG.Proof.X25519.Arm.rowC_le (hlx i hi) (hly j hj) (h.lt (i + j) (by omega))
  refine WP.append (carryPass_ok (rb := .r7) (o := ACC) (s0 := s2)
    (c := Radix16.rowC (accw s.mem (State.addr b)) (limbs s0.mem (State.addr b) x) (limbs s0.mem (State.addr b) y) i)
    (cin := 0) (by decide) (by omega) (by rw [e7, toNat7 hfit (by omega)]; omega)
    (fun k hk => by rw [P7, Offset.add_add]; exact hc2.inW (by omega))
    (by rw [hr2.gpr _ (by decide), h.r6]) (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : RowCtx b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [P7, Offset.add_add] at this
    change WP isa (.block [.ldr .r2 .r12 (4 * k), .mul .r2 .r1 .r2,
      .ldr .r3 .r7 (ACC + 4 * k), .dp .add .r3 .r3 (.reg .r2)]) s' _
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (y + 4 * k)) (by omega)
      (by rw [hp'.rest.gpr _ (by decide), e12, eaB hfit (by omega)]) (hc'.inR (by omega))
      fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by omega)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e7,
        ea7 hfit (by omega)]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega))
      fun t3 v3 => ?_
    refine wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r2).toNat = limbs s0.mem (State.addr b) y k := by
        rw [v1.gpr, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      have ea : (t1.gpr .r1).toNat = limbs s0.mem (State.addr b) x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      have hab := Nat.mul_le_mul (Nat.le_of_lt_succ (hlx i hi)) (Nat.le_of_lt_succ (hly k hk))
      have e2 : (t2.gpr .r2).toNat = limbs s0.mem (State.addr b) x i * limbs s0.mem (State.addr b) y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; omega), ea, ey]
      have e3 : (t3.gpr .r3).toNat = accw s.mem (State.addr b) (i + k) := by
        rw [v3.gpr, v2.mem, v1.mem, accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)]
        congr 1; omega
      have := hlt k hk
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r2 (by decide), toNat_add_lt (by rw [e3, e2]; simp only [Radix16.rowC] at this; omega), e3, e2,
        Radix16.rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    have hc3 : RowCtx b s3 := hc2.of_rest hp.rest (by decide)
    have e7' : s3.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hp.rest.gpr _ (by decide), e7]
    refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 112))) (by omega)
      (by rw [e7', ea7 hfit (by omega)]) (hc3.inW (by omega)) fun s4 u4 => ?_
    refine wp_dp (op2_imm (by decide)) fun s5 u5 => wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
    refine wp_dp (op2_reg _ _) fun s7 u7 => wp_cmp (op2_imm (by decide)) fun s8 u8 hz => ?_
    refine WP.block_nil ?_
    have hr6 : Rest (.lr :: fclob) s s8 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
          (u8.rest _))))))
    have hm6 : s8.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 112))) (s3.gpr .r5) := by
      rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem]
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 112⟩] s.mem s3.mem := by
      have := hp.frame; rw [P7, Offset.add_add] at this; rw [← hm2]; exact this
    have e7'' : s8.gpr .r7 = b + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [u8.gpr, u7.other _ (by decide), u6.other _ (by decide), u5.gpr, u4.gpr, e7']
      show b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
      rw [Offset.add_add, Nat.mul_succ]
    have e0 : s6.gpr .r0 = b := by
      rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, hc3.r0]
    have e2 : s7.gpr .r2 = BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [u7.gpr, u6.other _ (by decide), u5.gpr, u4.gpr, e7', e0]
      show b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 - b = _
      rw [Offset.add_add, Nat.mul_succ, BitVec.add_comm, BitVec.add_sub_cancel]
    -- The limbs of `ACC` after the row.
    have hacc : ∀ k < i + 29, accw s8.mem (State.addr b) k =
        Radix16.rowAcc (accw s.mem (State.addr b)) (limbs s0.mem (State.addr b) x) (limbs s0.mem (State.addr b) y) i k := by
      intro k hk
      rw [accw, hm6]
      rcases Nat.lt_or_ge k (i + 28) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)]
          simp only [Radix16.rowAcc, hki, ite_true]
        · have := hp.outs (k - i) (by omega)
          rw [P7, wd_shift, show 4 * i + (ACC + 4 * (k - i)) = ACC + 4 * k by omega] at this
          rw [this, out_zero]
          simp only [Radix16.rowAcc, show ¬ k < i by omega, hk', ite_false, ite_true]
      · rw [show ACC + 4 * k = 4 * i + (ACC + 112) by omega, wd_write_self, hp.r5, chain_zero]
        simp only [Radix16.rowAcc, show ¬ k < i by omega, show ¬ k < i + 28 by omega, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r7, .lr, .r2]).trans ((u5.rest (by decide)).trans
        ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans (u8.rest _))))) (by decide),
      h.rest.trans hr6, by rw [hr6.gpr _ (by decide), h.r6], e7'', ?_, ?_, ?_, fun k hk => ?_, ?_⟩, ?_⟩
    · rw [u8.gpr, u7.other _ (by decide), u6.gpr, u5.other _ (by decide), u4.gpr,
        hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.lr]
      show b + BitVec.ofNat 32 (x + 4 * i) + BitVec.ofNat 32 4 = _
      rw [Offset.add_add, Nat.mul_succ, Nat.add_assoc]
    · rw [hr6.gpr _ (by decide), h.r12]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · rw [hacc k hk]
      exact Radix16.rowAcc_lt (fun k hk => h.lt k (by omega)) (fun j hj => by have := hlt j hj; change _ ≤ 2 ^ 32 - 65536; omega) k hk
    · rw [Radix16.valN_congr hacc]; exact Radix16.row_val h.val
    · rw [hz, e2, show (112 : BitVec 32) = BitVec.ofNat 32 112 from rfl, sub_beq_zero (by omega) (by omega)]
      exact decide_eq_decide.mpr (by omega)

end VG.Proof.X448.Arm
