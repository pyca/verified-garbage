module
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field

import VerifiedGarbage.Proof.X25519.PPC64LE.AddSub
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# X25519 on PPC64LE: multiplication

`mulAt acc o x y` computes the 16 limbs of `[x] · [y]` at `acc`, row by row
(`row_ok`, the loop invariant `RowInv`: after `i` rows, `acc[0, i + 8)` holds
the limbs of `x_{<i} · y`), then stores at `o` a number congruent to it
(`mul_ok`), for any `acc` an offset reaches: X25519's `ACC` and Ed25519's.
Also the stores of one register into words (`stores_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P)

/-- Limb `k` of the product at `acc`. -/
def accw (acc : Nat) (m : Mem) (B : Addr) (k : Nat) : Nat := wd m B (acc + 4 * k)

theorem ACC_eq : ACC = 544 := rfl

theorem mul32_lt {a c : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) : a * c < 2 ^ 64 :=
  calc a * c ≤ a * 2 ^ 32 := Nat.mul_le_mul_left _ (Nat.le_of_lt hc)
    _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right ha (by decide)
    _ = 2 ^ 64 := (Nat.pow_add 2 32 32).symm

section
variable {b : Addr} {acc : Nat}

/-- Stores of register `r` into the `n` words from `o`. -/
theorem stores_ok {r : Reg} {o n : Nat} (ho : o + 4 * n ≤ 4096) {s : State} (hc : Ctx b s) :
    WP isa (.block (storeN r o n)) s fun s' =>
      (∀ j < n, wd s'.mem b (o + 4 * j) = (s.gpr r).toNat % 2 ^ 32) ∧
      Frame [⟨b + BitVec.ofNat 64 o, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s' := by
  unfold storeN
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun m s' => (∀ j < m, wd s'.mem b (o + 4 * j) = (s.gpr r).toNat % 2 ^ 32) ∧
      Frame [⟨b + BitVec.ofNat 64 o, 4 * m⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun m s' hm ⟨h1, h2, h3, h4⟩ => ?_) n (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩) fun s' h => h
  refine sw0_ok (hc.of_rest h4 (by decide)) (d := o + 4 * m) (by omega_using [ho, hm]) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, by rw [u2.gpr, h3], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega_using [ho, hm, hj]) (by omega_using [ho, hm])]; exact h1 j hj
    · rw [wd_write_self, h3, toNat_lo32]
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho, hm]))

theorem zeroAcc_ok (hA : acc + 64 ≤ 4096) {s : State} (hc : Ctx b s) :
    WP isa (.block (zeroAcc acc)) s fun s' => (∀ j < 8, accw acc s'.mem b j = 0) ∧
      Frame [⟨b + BitVec.ofNat 64 acc, 32⟩] s.mem s'.mem ∧ Rest [.r7] s s' := by
  unfold zeroAcc
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r7]) (by decide)) (by decide)
  refine WP.mono (stores_ok (r := .r7) (o := acc) (n := 8) (by omega) hc1) fun s' ⟨h1, h2, _, h4⟩ =>
    ⟨fun j hj => by rw [accw, h1 j hj, u1.gpr]; rfl, by rw [← u1.mem]; exact h2,
      (u1.rest (by decide)).trans (h4.mono (by decide))⟩

/-- The loop invariant of the rows of `mul o x y` from `s0`, after `i` rows. -/
structure RowInv (acc : Nat) (b : Addr) (x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob s0 s
  r10 : s.gpr .r10 = 38
  r9 : s.gpr .r9 = b + BitVec.ofNat 64 (4 * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (8 - i)
  frame : Frame [⟨b + BitVec.ofNat 64 acc, 64⟩] s0.mem s.mem
  val : val32 (accw acc s.mem b) (i + 8) = val32 (limb s0.mem b x) i * V s0.mem b y

theorem mulPre_ok (hA : acc + 64 ≤ 4096) {x y : Nat} {s : State} (hc : Ctx b s) :
    WP isa (.block (prologue ++ zeroAcc acc ++ ([.addi .r9 .r6 0, .li .r11 8] : List Instr))) s
      (RowInv acc b x y s 0) := by
  rw [List.append_assoc]
  refine WP.append prologue_ok fun s1 ⟨h10, _, hr1, hm1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (zeroAcc_ok hA hc1) fun s2 ⟨hz, hf2, hr2⟩ => ?_
  have hc2 : Ctx b s2 := hc1.of_rest hr2 (by decide)
  refine wp_addi (by decide) (by decide) fun s3 u3 => wp_li (by decide) fun s4 u4 => WP.block_nil ?_
  have hr : Rest clob s s4 :=
    (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide))))
  have hr' : Rest [.r7, .r9, .r11] s1 s4 :=
    (hr2.mono (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have hm4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  refine ⟨hc.of_rest hr (by decide), hr, by rw [hr'.gpr _ (by decide), h10], ?_, u4.gpr, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.gpr, hc2.r6]
  · rw [hm4, ← hm1]; exact hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  · rw [hm4, val32_congr (g := fun _ => 0) (fun k hk => hz k hk), val32_zero_fn]
    exact (Nat.zero_mul _).symm

theorem row_ok (hA : acc + 64 ≤ 4096) {x y : Nat} (hx : x + 32 ≤ acc) (hy : y + 32 ≤ acc)
    {s0 : State} {i : Nat} (hi : i < 8) {s : State} (h : RowInv acc b x y s0 i s) :
    WP isa (.block (row acc x y)) s fun s' =>
      RowInv acc b x y s0 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (8 - (i + 1) ≠ 0) := by
  have hframe0 : ∀ z : Nat, z + 32 ≤ acc → ∀ k < 8,
      limb s.mem b z k = limb s0.mem b z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [row, List.cons_append, List.nil_append]
  refine wp_lw (a := b + BitVec.ofNat 64 (x + 4 * i)) (by decide) (by omega_arith)
    (by rw [h.r9, Offset.add_add, Nat.add_comm]) (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  have hr2 : Rest [.r4, .r8] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e1 : (s2.gpr .r4).toNat = limb s0.mem b x i := by
    rw [u2.other _ (by decide), u1.gpr, toNat_ext32, ← hframe0 x hx i hi]; rfl
  have e9 : s2.gpr .r9 = b + BitVec.ofNat 64 (4 * i) := by rw [hr2.gpr _ (by decide), h.r9]
  have hlt : ∀ j < 8, rowC (accw acc s.mem b) (limb s0.mem b x) (limb s0.mem b y) i j + 2 ^ 32 ≤ 2 ^ 64 :=
    fun j _ => rowC_le (limb_lt _ _ _ _) (limb_lt _ _ _ _) (wd_lt _ _ _)
  refine WP.append (pass_ok (rb := .r9) (o := acc) (s0 := s2)
    (c := rowC (accw acc s.mem b) (limb s0.mem b x) (limb s0.mem b y) i)
    (cin := 0) (by decide) (by decide) (by omega_arith)
    (fun k hk => by rw [e9, Offset.add_add]; exact hc2.inW (by omega_arith))
    (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : Ctx b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨b + BitVec.ofNat 64 (4 * i + acc), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [e9, Offset.add_add] at this
    simp only [rowSrc]
    refine lw0_ok hc' (d := y + 4 * k) (by omega_arith) fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_lw (a := b + BitVec.ofNat 64 (4 * i + (acc + 4 * k))) (by decide) (by omega_arith)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e9,
        Offset.add_add]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega_arith))
      fun t3 v3 => ?_
    refine wp_add fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r5).toNat = limb s0.mem b y k := by
        rw [v1.gpr, toNat_ext32, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      have ea : (t1.gpr .r4).toNat = limb s0.mem b x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      have e2 : (t2.gpr .r5).toNat = limb s0.mem b x i * limb s0.mem b y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; exact mul32_lt (limb_lt _ _ _ _) (limb_lt _ _ _ _)), ea, ey]
      have e3 : (t3.gpr .r7).toNat = accw acc s.mem b (i + k) := by
        rw [v3.gpr, toNat_ext32, v2.mem, v1.mem, accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)]
        congr 1; omega_arith
      have := hlt k hk
      rw [v4.gpr, v3.other .r5 (by decide)]
      rw [toNat_add_lt (by rw [e3, e2]; simp only [rowC] at this; omega_arith), e3, e2,
        rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    have hc3 : Ctx b s3 := hc2.of_rest hp.rest (by decide)
    have e9' : s3.gpr .r9 = b + BitVec.ofNat 64 (4 * i) := by rw [hp.rest.gpr _ (by decide), e9]
    refine wp_sw (a := b + BitVec.ofNat 64 (4 * i + (acc + 32))) (by decide) (by omega_arith)
      (by rw [e9', Offset.add_add]) (hc3.inW (by omega_arith)) fun s4 u4 => ?_
    refine wp_addi (by decide) (by decide) fun s5 u5 => wp_subi (by decide) (by decide) fun s6 u6 => ?_
    refine WP.block_nil ?_
    have hr6 : Rest [.r4, .r5, .r7, .r8, .r9, .r11] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans (u6.rest (by decide)))))
    have hm6 : s6.mem = s3.mem.writeW (b + BitVec.ofNat 64 (4 * i + (acc + 32))) ((s3.gpr .r8).setWidth 32) := by
      rw [u6.mem, u5.mem, u4.mem]
    have hpf : Frame [⟨b + BitVec.ofNat 64 (4 * i + acc), 32⟩] s.mem s3.mem := by
      have := hp.frame; rw [e9, Offset.add_add] at this; rw [← hm2]; exact this
    have hr11 : s6.gpr .r11 = BitVec.ofNat 64 (8 - (i + 1)) := by
      rw [u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.r11,
        ofNat_sub_one (by omega_arith) (by omega_arith)]
      congr 1
    have hch := chain_lt (cin := 0) hlt (by decide) 8 (Nat.le_refl _)
    -- The limbs of `acc` after the row.
    have hacc : ∀ k < i + 9, accw acc s6.mem b k =
        rowAcc (accw acc s.mem b) (limb s0.mem b x) (limb s0.mem b y) i k := by
      intro k hk
      rw [accw, hm6]
      rcases Nat.lt_or_ge k (i + 8) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]
          simp only [rowAcc, hki, ite_true]; rfl
        · have := hp.outs (k - i) (by omega_arith)
          rw [e9, wd_shift, show 4 * i + (acc + 4 * (k - i)) = acc + 4 * k by omega_arith] at this
          rw [this]
          simp only [rowAcc, show ¬ k < i by omega_arith, hk', ite_false, ite_true]
      · rw [show acc + 4 * k = 4 * i + (acc + 32) by omega_arith, wd_write_self, toNat_lo32, hp.r8,
          Nat.mod_eq_of_lt hch]
        simp only [rowAcc, show ¬ k < i by omega_arith, show ¬ k < i + 8 by omega_arith, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r9, .r11]).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
        (by decide), h.rest.trans (hr6.mono (by decide)), by rw [hr6.gpr _ (by decide), h.r10],
      ?_, hr11, ?_, ?_⟩, ?_⟩
    · rw [u6.other _ (by decide), u5.gpr, u4.gpr, e9', Offset.add_add, Nat.mul_succ]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [val32_congr hacc]; exact row_val h.val
    · rw [hr11, ofNat_ne_zero (by omega_arith)]

theorem mul_ok (hA : acc + 64 ≤ 4096) {o x y : Nat} (ho : o + 32 ≤ acc) (hx : x + 32 ≤ acc)
    (hy : y + 32 ≤ acc) {s : State} (hc : Ctx b s) :
    WP isa (mulAt acc o x y) s fun s' =>
      Rest clob s s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 acc, 64⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := by
  unfold mulAt
  refine WP.seq (WP.mono (mulPre_ok hA (x := x) (y := y) hc) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (Q := RowInv acc b x y s 8) (WP.loop (M := isa)
    (fun n s' => ∃ i, n = 8 - i ∧ i < 8 ∧ RowInv acc b x y s i s') ?_ 8 s1 ⟨0, rfl, by decide, h1⟩)
    fun s2 h2 => ?_)
  · rintro n s' ⟨i, rfl, hi, hr⟩
    refine WP.mono (row_ok hA hx hy hi hr) fun s'' ⟨hr', hz⟩ => ?_
    by_cases h8 : i + 1 = 8
    · refine .inl ⟨by rw [eval_nonzero, hz]; simp [h8], ?_⟩
      rw [h8] at hr'; exact hr'
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 8 - (i + 1), by omega_arith, i + 1, rfl,
        by omega_arith, hr'⟩
  · refine wp_li (by decide) fun s3 u3 => ?_
    have hc3 : Ctx b s3 := h2.ctx.of_rest (u3.rest (ws := [.r8]) (by decide)) (by decide)
    have hl16 : ∀ k < 16, accw acc s2.mem b k < 2 ^ 32 := fun k _ => wd_lt _ _ _
    have hv : val32 (accw acc s2.mem b) 16 = V s.mem b x * V s.mem b y := h2.val
    have hlo := val32_lt (f := accw acc s2.mem b) (n := 8) fun k hk => hl16 k (by omega_arith)
    have hhi := val32_lt (f := fun k => accw acc s2.mem b (8 + k)) (n := 8) fun k hk =>
      hl16 (8 + k) (by omega_arith)
    refine WP.mono (passTail'_ok (c := foldC (accw acc s2.mem b)) (by omega_arith)
      (foldC_le hl16) (by rw [val32_foldC]; rw [show 32 * 8 = 256 from rfl] at hlo hhi; omega_arith) hc3
      (by rw [u3.other _ (by decide), h2.r10]) u3.gpr ?_)
      fun s4 ⟨hr4, hf4, hv4⟩ => ⟨h2.rest.trans ((u3.rest (by decide)).trans (hr4.mono (by decide))),
        ?_, ?_⟩
    · intro k hk s' hp
      have hc' : Ctx b s' := hc3.of_rest hp.rest (by decide)
      refine lw0_ok hc' (d := acc + 4 * k) (by omega_arith) fun t1 v1 => ?_
      refine lw0_ok (hc'.of_rest (v1.rest (ws := [.r7]) (by decide)) (by decide)) (d := acc + 32 + 4 * k)
        (by omega_arith) fun t2 v2 => ?_
      refine wp_mul fun t3 v3 => wp_add fun t4 v4 => WP.block_nil ⟨?_, ?_, by
        rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
      · have el : (t1.gpr .r7).toNat = accw acc s2.mem b k := by
          rw [v1.gpr, toNat_ext32]; show wd s'.mem _ _ = _
          rw [wd_pass hc3 hp.frame (by omega_arith) (by omega_arith) (by omega_arith), u3.mem]; rfl
        have eh : (t2.gpr .r5).toNat = accw acc s2.mem b (8 + k) := by
          rw [v2.gpr, toNat_ext32, v1.mem]; show wd s'.mem _ _ = _
          rw [wd_pass hc3 hp.frame (by omega_arith) (by omega_arith) (by omega_arith), u3.mem, accw]
          congr 1; omega_arith
        have h10 : t2.gpr .r10 = 38 := by
          rw [v2.other _ (by decide), v1.other _ (by decide), hp.rest.gpr _ (by decide),
            u3.other _ (by decide), h2.r10]
        have hh := hl16 (8 + k) (by omega_arith)
        have hl := hl16 k (by omega_arith)
        have t38 : (38 : BitVec 64).toNat = 38 := rfl
        have e3 : (t3.gpr .r5).toNat = accw acc s2.mem b (8 + k) * 38 := by
          rw [v3.gpr, h10, toNat_mul_lt (by rw [eh, t38]; omega_arith), eh, t38]
        rw [v4.gpr, v3.other .r7 (by decide), v2.other .r7 (by decide),
          toNat_add_lt (by rw [el, e3]; omega_arith), el, e3, foldC, Nat.mul_comm 38]
      · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
          (v4.rest (by decide))))
    · have hf2 : Frame [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 acc, 64⟩]
          s.mem s2.mem := h2.frame.mono fun r hr => by simp [List.mem_singleton.mp hr]
      rw [u3.mem] at hf4
      exact hf2.trans (hf4.mono fun r hr => by simp [List.mem_singleton.mp hr])
    · rw [hv4, val32_foldC, ← hv, show (16 : Nat) = 8 + 8 from rfl, val32_append, Proof.X25519.fold256]

end

end VG.Proof.X25519.PPC64LE
