module
public import VerifiedGarbage.Proof.X448.RISCV64.Field
public import VerifiedGarbage.Proof.X25519.RISCV64.Mul

import VerifiedGarbage.Proof.X448.RISCV64.AddSub
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X448.RISCV64.Pass

/-!
# X448 on RISCV64: multiplication

`mul o x y` computes the 28 limbs of `[x] · [y]` at `ACC`, row by row
(`row_ok`, the loop invariant `RowInv`: after `i` rows, `ACC[0, i + 14)`
holds the limbs of `x_{<i} · y`), then stores at `o` a number congruent to it
(`mul_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Spec.X448 (P)

theorem ACC_eq : ACC = 952 := rfl

section
variable {b : Addr}

theorem zeroAcc_ok {s : State} (hc : Ctx b s) :
    WP isa (.block zeroAcc) s fun s' => (∀ j < 14, accw ACC s'.mem b j = 0) ∧
      Frame [⟨b + BitVec.ofNat 64 ACC, 56⟩] s.mem s'.mem ∧ Rest [.a4] s s' := by
  unfold zeroAcc
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.a4]) (by decide)) (by decide)
  refine WP.mono (stores_ok (r := .a4) (o := ACC) (n := 14) (by decide) (by decide) hc1) fun s' ⟨h1, h2, _, h4⟩ =>
    ⟨fun j hj => by rw [accw, h1 j hj, u1.gpr]; rfl, by rw [← u1.mem]; exact h2,
      (u1.rest (by decide)).trans (h4.mono (by decide))⟩

/-- The loop invariant of the rows of `mul o x y` from `s0`, after `i` rows. -/
structure RowInv (b : Addr) (x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob s0 s
  a6 : s.gpr .a6 = b + BitVec.ofNat 64 (4 * i)
  t0 : s.gpr .t0 = BitVec.ofNat 64 (14 - i)
  frame : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem
  val : val32 (accw ACC s.mem b) (i + 14) = val32 (limb s0.mem b x) i * V s0.mem b y

theorem mulPre_ok {x y : Nat} {s : State} (hc : Ctx b s) :
    WP isa (.block (zeroAcc ++ ([.addi .a6 .a3 0, .li .t0 14] : List Instr))) s
      (RowInv b x y s 0) := by
  refine WP.append (zeroAcc_ok hc) fun s2 ⟨hz, hf2, hr2⟩ => ?_
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine wp_addi (by decide) fun s3 u3 => wp_li (by decide) fun s4 u4 => WP.block_nil ?_
  have hr : Rest clob s s4 :=
    (hr2.mono (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have hm4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  refine ⟨hc.of_rest hr (by decide), hr, ?_, u4.gpr, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.gpr, hc2.a3]
  · rw [hm4]; exact hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  · rw [hm4, val32_congr (g := fun _ => 0) (fun k hk => hz k hk), val32_zero_fn]
    exact (Nat.zero_mul _).symm

theorem row_ok {x y : Nat} (hx : x + 56 ≤ ACC) (hy : y + 56 ≤ ACC) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0)
    {s0 : State} {i : Nat} (hi : i < 14) {s : State} (h : RowInv b x y s0 i s) :
    WP isa (.block (row x y)) s fun s' =>
      RowInv b x y s0 (i + 1) s' ∧ (s'.gpr .t0 != 0) = decide (14 - (i + 1) ≠ 0) := by
  have hA := ACC_eq
  have hframe0 : ∀ z : Nat, z + 56 ≤ ACC → ∀ k < 14,
      limb s.mem b z k = limb s0.mem b z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [row, List.cons_append, List.nil_append]
  refine wp_lw (a := b + BitVec.ofNat 64 (x + 4 * i)) (by omega_arith)
    (by rw [h.a6, Offset.add_add, Nat.add_comm]) (al4 h.ctx.al (by omega_arith)) (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  have hr2 : Rest [.a1, .a5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e1 : (s2.gpr .a1).toNat = limb s0.mem b x i := by
    rw [u2.other _ (by decide), u1.gpr, toNat_ext32, ← hframe0 x hx i hi]; rfl
  have e9 : s2.gpr .a6 = b + BitVec.ofNat 64 (4 * i) := by rw [hr2.gpr _ (by decide), h.a6]
  have hlt : ∀ j < 14, rowC (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i j + 2 ^ 32 ≤ 2 ^ 64 :=
    fun j _ => rowC_le (limb_lt _ _ _ _) (limb_lt _ _ _ _) (wd_lt _ _ _)
  refine WP.append (pass_ok (rb := .a6) (o := ACC) (s0 := s2)
    (c := rowC (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i)
    (cin := 0) (by decide) (by omega_arith)
    (fun k hk => by rw [e9, Offset.add_add]; exact hc2.inW (by omega_arith))
    (fun k hk => by rw [e9, Offset.add_add]; exact al4 hc2.al (by omega_arith))
    (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : Ctx b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [e9, Offset.add_add] at this
    simp only [rowSrc]
    refine lw0_ok hc' (d := y + 4 * k) (by omega_arith) (by omega_arith) fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_lw (a := b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by omega_arith)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e9,
        Offset.add_add]) (al4 hc'.al (by omega_arith)) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega_arith))
      fun t3 v3 => ?_
    refine wp_add fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .a2).toNat = limb s0.mem b y k := by
        rw [v1.gpr, toNat_ext32, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      have ea : (t1.gpr .a1).toNat = limb s0.mem b x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      have e2 : (t2.gpr .a2).toNat = limb s0.mem b x i * limb s0.mem b y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; exact mul32_lt (limb_lt _ _ _ _) (limb_lt _ _ _ _)), ea, ey]
      have e3 : (t3.gpr .a4).toNat = accw ACC s.mem b (i + k) := by
        rw [v3.gpr, toNat_ext32, v2.mem, v1.mem, accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)]
        congr 1; omega_arith
      have := hlt k hk
      rw [v4.gpr, v3.other .a2 (by decide)]
      rw [toNat_add_lt (by rw [e3, e2]; simp only [rowC] at this; omega_arith), e3, e2,
        rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    have hc3 : Ctx b s3 := hc2.of_rest hp.rest (by decide)
    have e9' : s3.gpr .a6 = b + BitVec.ofNat 64 (4 * i) := by rw [hp.rest.gpr _ (by decide), e9]
    refine wp_stw (a := b + BitVec.ofNat 64 (4 * i + (ACC + 56))) (by omega_arith)
      (by rw [e9', Offset.add_add]) (al4 hc3.al (by omega_arith)) (hc3.inW (by omega_arith)) fun s4 u4 => ?_
    refine wp_addi (by decide) fun s5 u5 => wp_subi (by decide) fun s6 u6 => ?_
    refine WP.block_nil ?_
    have hr6 : Rest [.a1, .a2, .a4, .a5, .a6, .t0] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans (u6.rest (by decide)))))
    have hm6 : s6.mem = s3.mem.writeW (b + BitVec.ofNat 64 (4 * i + (ACC + 56))) ((s3.gpr .a5).setWidth 32) := by
      rw [u6.mem, u5.mem, u4.mem]
    have hpf : Frame [⟨b + BitVec.ofNat 64 (4 * i + ACC), 56⟩] s.mem s3.mem := by
      have := hp.frame; rw [e9, Offset.add_add] at this; rw [← hm2]; exact this
    have hr11 : s6.gpr .t0 = BitVec.ofNat 64 (14 - (i + 1)) := by
      rw [u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.t0,
        ofNat_sub_one (by omega_arith) (by omega_arith)]
      congr 1
    have hch := chain_lt (cin := 0) hlt (by decide) 14 (Nat.le_refl _)
    -- The limbs of `ACC` after the row.
    have hacc : ∀ k < i + 15, accw ACC s6.mem b k =
        rowAcc (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i k := by
      intro k hk
      rw [accw, hm6]
      rcases Nat.lt_or_ge k (i + 14) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]
          simp only [rowAcc, hki, ite_true]; rfl
        · have := hp.outs (k - i) (by omega_arith)
          rw [e9, wd_shift, show 4 * i + (ACC + 4 * (k - i)) = ACC + 4 * k by omega_arith] at this
          rw [this]
          simp only [rowAcc, show ¬ k < i by omega_arith, hk', ite_false, ite_true]
      · rw [show ACC + 4 * k = 4 * i + (ACC + 56) by omega_arith, wd_write_self, toNat_lo32, hp.a5,
          Nat.mod_eq_of_lt hch]
        simp only [rowAcc, show ¬ k < i by omega_arith, show ¬ k < i + 14 by omega_arith, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.a6, .t0]).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
        (by decide), h.rest.trans (hr6.mono (by decide)), ?_, hr11, ?_, ?_⟩, ?_⟩
    · rw [u6.other _ (by decide), u5.gpr, u4.gpr, e9', Offset.add_add, Nat.mul_succ]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [val32_congr hacc]; exact row_val h.val
    · rw [hr11, ofNat_ne_zero (by omega_arith)]

/-- A word of `ACC`, through a pass at `o` below it. -/
theorem wd_acc {s0 s : State} (hc : Ctx b s0) {o k j : Nat} (ho : o + 56 ≤ ACC) (hk : k < 14)
    (hj : j < 28) (hf : Frame [⟨s0.gpr .a3 + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem) :
    wd s.mem b (ACC + 4 * j) = accw ACC s0.mem b j := by
  have hA := ACC_eq
  exact wd_pass hc hf (.inr (by omega_arith)) (by omega_arith) (by omega_arith)

theorem mul_ok {o x y : Nat} (ho : o + 56 ≤ ACC) (hx : x + 56 ≤ ACC)
    (hy : y + 56 ≤ ACC) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (mul o x y) s fun s' =>
      Rest clob s s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := by
  have hA := ACC_eq
  unfold mul
  refine WP.seq (WP.mono (mulPre_ok (x := x) (y := y) hc) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (Q := RowInv b x y s 14) (WP.loop (M := isa)
    (fun n s' => ∃ i, n = 14 - i ∧ i < 14 ∧ RowInv b x y s i s') ?_ 14 s1 ⟨0, rfl, by decide, h1⟩)
    fun s2 h2 => ?_)
  · rintro n s' ⟨i, rfl, hi, hr⟩
    refine WP.mono (row_ok hx hy hx4 hy4 hi hr) fun s'' ⟨hr', hz⟩ => ?_
    by_cases h14 : i + 1 = 14
    · refine .inl ⟨by rw [eval_nonzero, hz]; simp [h14], ?_⟩
      rw [h14] at hr'; exact hr'
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 14 - (i + 1), by omega_arith, i + 1, rfl,
        by omega_arith, hr'⟩
  · rw [List.cons_append]
    refine wp_li (by decide) fun s3 u3 => ?_
    have hc3 : Ctx b s3 := h2.ctx.of_rest (u3.rest (ws := [.a5]) (by decide)) (by decide)
    have hl28 : ∀ k < 28, accw ACC s2.mem b k < 2 ^ 32 := fun k _ => wd_lt _ _ _
    have hv : val32 (accw ACC s2.mem b) 28 = V s.mem b x * V s.mem b y := h2.val
    obtain ⟨hfb, hfv⟩ := foldC_facts hl28
    refine WP.mono (passTail_ok (c := foldC (accw ACC s2.mem b)) (by omega_arith) ho4
      (foldC_le hl28) hfb hc3 u3.gpr ?_)
      fun s4 ⟨hr4, hf4, hv4⟩ => ⟨h2.rest.trans ((u3.rest (by decide)).trans (hr4.mono (by decide))),
        ?_, ?_⟩
    · intro k hk s' hp
      have hc' : Ctx b s' := hc3.of_rest hp.rest (by decide)
      have hacc : ∀ j < 28, wd s'.mem b (ACC + 4 * j) = accw ACC s2.mem b j := fun j hj => by
        rw [wd_acc hc3 ho hk hj hp.frame, accw, accw, u3.mem]
      have lo : ∀ (t : State) (j : Nat), j < 28 → Rest [.a2, .a4] s' t → t.mem = s'.mem → ∀ (r : Reg) (d : Nat),
          d = ACC + 4 * j → ∀ (is : List Instr) (Q : State → Prop),
          (∀ t', Upd t t' r (BitVec.ofNat 64 (accw ACC s2.mem b j)) → WP isa (.block is) t' Q) →
          WP isa (.block (.load .w r .a3 d :: is)) t Q := by
        intro t j hj hr hm r d hd is Q k
        subst hd
        refine lw0_ok (hc'.of_rest hr (by decide)) (by omega_arith) (by omega_arith) fun t' u => k t' ?_
        have e : (t.mem.readW (b + BitVec.ofNat 64 (ACC + 4 * j)) 32).setWidth 64 =
            BitVec.ofNat 64 (accw ACC s2.mem b j) := by
          apply BitVec.eq_of_toNat_eq
          rw [toNat_ext32, hm, toNat_imm (v := accw ACC s2.mem b j) (Nat.lt_trans (wd_lt _ _ _) (by decide))]
          exact hacc j hj
        rw [← e]; exact u
      have hl := hl28 k (by omega_arith)
      have hh := hl28 (14 + k) (by omega_arith)
      unfold mulSrc
      by_cases h7 : k < 7
      · simp only [h7, ite_true, List.cons_append, List.nil_append]
        have hh' := hl28 (14 + (k + 7)) (by omega_arith)
        refine lo s' k (by omega_arith) (Rest.refl _ _) rfl _ _ rfl _ _ fun t1 v1 => ?_
        refine lo t1 (14 + k) (by omega_arith) (v1.rest (by decide)) v1.mem _ _ (by omega_arith) _ _ fun t2 v2 => ?_
        refine wp_add fun t3 v3 => ?_
        refine lo t3 (14 + (k + 7)) (by omega_arith)
          ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide))))
          (by rw [v3.mem, v2.mem, v1.mem]) _ _ (by omega_arith) _ _ fun t4 v4 => ?_
        refine wp_add fun t5 v5 => WP.block_nil ⟨?_, ?_, by rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩
        · have e3 : (t3.gpr .a4).toNat = accw ACC s2.mem b k + accw ACC s2.mem b (14 + k) := by
            rw [v3.gpr, v2.other .a4 (by decide), v1.gpr, v2.gpr, toNat_add_lt (by
              rw [toNat_imm (by omega_arith), toNat_imm (by omega_arith)]; omega_arith),
              toNat_imm (by omega_arith), toNat_imm (by omega_arith)]
          rw [v5.gpr, v4.other .a4 (by decide), v4.gpr, toNat_add_lt (by
            rw [e3, toNat_imm (by omega_arith)]; omega_arith), e3, toNat_imm (by omega_arith), foldC]
          simp only [h7, ite_true]
        · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
            ((v4.rest (by decide)).trans (v5.rest (by decide)))))
      · simp only [h7, ite_false, List.cons_append, List.nil_append]
        have hh' := hl28 (14 + (k - 7)) (by omega_arith)
        refine lo s' k (by omega_arith) (Rest.refl _ _) rfl _ _ rfl _ _ fun t1 v1 => ?_
        refine lo t1 (14 + k) (by omega_arith) (v1.rest (by decide)) v1.mem _ _ (by omega_arith) _ _ fun t2 v2 => ?_
        refine wp_add fun t3 v3 => wp_add fun t3' v3' => ?_
        have hr3 : Rest [.a2, .a4] s' t3' :=
          (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
            (v3'.rest (by decide))))
        refine lo t3' (14 + (k - 7)) (by omega_arith) hr3 (by rw [v3'.mem, v3.mem, v2.mem, v1.mem]) _ _
          (by omega_arith) _ _ fun t4 v4 => ?_
        refine wp_add fun t5 v5 => WP.block_nil ⟨?_, hr3.trans ((v4.rest (by decide)).trans (v5.rest (by decide))),
          by rw [v5.mem, v4.mem, v3'.mem, v3.mem, v2.mem, v1.mem]⟩
        have e5 : (t3.gpr .a2).toNat = accw ACC s2.mem b (14 + k) := by
          rw [v3.other .a2 (by decide), v2.gpr, toNat_imm (by omega_arith)]
        have e3 : (t3.gpr .a4).toNat = accw ACC s2.mem b k + accw ACC s2.mem b (14 + k) := by
          rw [v3.gpr, v2.other .a4 (by decide), v1.gpr, v2.gpr, toNat_add_lt (by
            rw [toNat_imm (by omega_arith), toNat_imm (by omega_arith)]; omega_arith),
            toNat_imm (by omega_arith), toNat_imm (by omega_arith)]
        have e3' : (t3'.gpr .a4).toNat = accw ACC s2.mem b k + accw ACC s2.mem b (14 + k) +
            accw ACC s2.mem b (14 + k) := by
          rw [v3'.gpr, toNat_add_lt (by rw [e3, e5]; omega_arith), e3, e5]
        rw [v5.gpr, v4.other .a4 (by decide), v4.gpr, toNat_add_lt (by
          rw [e3', toNat_imm (by omega_arith)]; omega_arith), e3', toNat_imm (by omega_arith), foldC]
        simp only [h7, ite_false]
    · have hf2 : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩]
          s.mem s2.mem := h2.frame.mono fun r hr => by simp [List.mem_singleton.mp hr]
      rw [u3.mem] at hf4
      exact hf2.trans (hf4.mono fun r hr => by simp [List.mem_singleton.mp hr])
    · rw [hv4, hfv, hv]

end

end VG.Proof.X448.RISCV64
