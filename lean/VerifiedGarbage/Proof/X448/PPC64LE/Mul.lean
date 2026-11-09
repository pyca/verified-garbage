module
public import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
public import VerifiedGarbage.Proof.X25519.PPC64LE.Product

public import VerifiedGarbage.Proof.X448.PPC64LE.AddSub
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X448.PPC64LE.Pass
import VerifiedGarbage.Proof.X448.PPC64LE.Product
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill

/-!
# X448 on PPC64LE: multiplication

`mul o x y` computes the 28 limbs of `[x] · [y]` at `ACC`, as fourteen
doublewords row by row (`rows64_ok`, with `row64_ok` of
`Proof/X448/PPC64LE/Product.lean`),
then stores at `o` a number congruent to it by three carry chains and
two folds (`reduce_ok`, `mul_ok`). Also the rows of a
product of limbs (`row_ok`, the loop invariant `RowInv`: after `i` rows,
`ACC[0, i + 14)` holds the limbs of `x_{<i} · y`), which Ed448's scalar
arithmetic uses.

`mulX_ok`: `mulX` (`mulP`) computes the same in registers, which it does
not restore (`clobR`): it loads the operands (`ldsAt_ok`), computes the
product's fourteen doublewords (`columns_ok`,
`Proof/X448/PPC64LE/Product.lean`), reduces them by three carry chains and
two folds (`chainN_ok`, `rotsN_ok`, `reduceR_ok`, whose arithmetic is
`reduce_arith`), and stores the result (`stdsAt_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P)

theorem ACC_eq : ACC = 952 := rfl

section
variable {b : Addr}

theorem zeroAcc_ok {s : State} (hc : Ctx b s) :
    WP isa (.block zeroAcc) s fun s' => (∀ j < 14, accw ACC s'.mem b j = 0) ∧
      Frame [⟨b + BitVec.ofNat 64 ACC, 56⟩] s.mem s'.mem ∧ Rest [.r7] s s' := by
  unfold zeroAcc
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r7]) (by decide)) (by decide)
  refine WP.mono (stores_ok (r := .r7) (o := ACC) (n := 14) (by decide) hc1) fun s' ⟨h1, h2, _, h4⟩ =>
    ⟨fun j hj => by rw [accw, h1 j hj, u1.gpr]; rfl, by rw [← u1.mem]; exact h2,
      (u1.rest (by decide)).trans (h4.mono (by decide))⟩

/-- The loop invariant of the rows of `mul o x y` from `s0`, after `i` rows. -/
structure RowInv (b : Addr) (x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob s0 s
  r9 : s.gpr .r9 = b + BitVec.ofNat 64 (4 * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (14 - i)
  frame : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem
  val : val32 (accw ACC s.mem b) (i + 14) = val32 (limb s0.mem b x) i * V s0.mem b y

theorem mulPre_ok {x y : Nat} {s : State} (hc : Ctx b s) :
    WP isa (.block (zeroAcc ++ ([.addi .r9 .r6 0, .li .r11 14] : List Instr))) s
      (RowInv b x y s 0) := by
  refine WP.append (zeroAcc_ok hc) fun s2 ⟨hz, hf2, hr2⟩ => ?_
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine wp_addi (by decide) (by decide) fun s3 u3 => wp_li (by decide) fun s4 u4 => WP.block_nil ?_
  have hr : Rest clob s s4 :=
    (hr2.mono (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have hm4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  refine ⟨hc.of_rest hr (by decide), hr, ?_, u4.gpr, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.gpr, hc2.r6]
  · rw [hm4]; exact hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  · rw [hm4, val32_congr (g := fun _ => 0) (fun k hk => hz k hk), val32_zero_fn]
    exact (Nat.zero_mul _).symm

theorem row_ok {x y : Nat} (hx : x + 56 ≤ ACC) (hy : y + 56 ≤ ACC)
    {s0 : State} {i : Nat} (hi : i < 14) {s : State} (h : RowInv b x y s0 i s) :
    WP isa (.block (row x y)) s fun s' =>
      RowInv b x y s0 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (14 - (i + 1) ≠ 0) := by
  have hA := ACC_eq
  have hframe0 : ∀ z : Nat, z + 56 ≤ ACC → ∀ k < 14,
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
  have hlt : ∀ j < 14, rowC (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i j + 2 ^ 32 ≤ 2 ^ 64 :=
    fun j _ => rowC_le (limb_lt _ _ _ _) (limb_lt _ _ _ _) (wd_lt _ _ _)
  refine WP.append (pass_ok (rb := .r9) (o := ACC) (s0 := s2)
    (c := rowC (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i)
    (cin := 0) (by decide) (by decide) (by omega_arith)
    (fun k hk => by rw [e9, Offset.add_add]; exact hc2.inW (by omega_arith))
    (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : Ctx b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [e9, Offset.add_add] at this
    simp only [rowSrc]
    refine lw0_ok hc' (d := y + 4 * k) (by omega_arith) fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_lw (a := b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by decide) (by omega_arith)
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
      have e3 : (t3.gpr .r7).toNat = accw ACC s.mem b (i + k) := by
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
    refine wp_sw (a := b + BitVec.ofNat 64 (4 * i + (ACC + 56))) (by decide) (by omega_arith)
      (by rw [e9', Offset.add_add]) (hc3.inW (by omega_arith)) fun s4 u4 => ?_
    refine wp_addi (by decide) (by decide) fun s5 u5 => wp_subi (by decide) (by decide) fun s6 u6 => ?_
    refine WP.block_nil ?_
    have hr6 : Rest [.r4, .r5, .r7, .r8, .r9, .r11] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans (u6.rest (by decide)))))
    have hm6 : s6.mem = s3.mem.writeW (b + BitVec.ofNat 64 (4 * i + (ACC + 56))) ((s3.gpr .r8).setWidth 32) := by
      rw [u6.mem, u5.mem, u4.mem]
    have hpf : Frame [⟨b + BitVec.ofNat 64 (4 * i + ACC), 56⟩] s.mem s3.mem := by
      have := hp.frame; rw [e9, Offset.add_add] at this; rw [← hm2]; exact this
    have hr11 : s6.gpr .r11 = BitVec.ofNat 64 (14 - (i + 1)) := by
      rw [u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.r11,
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
      · rw [show ACC + 4 * k = 4 * i + (ACC + 56) by omega_arith, wd_write_self, toNat_lo32, hp.r8,
          Nat.mod_eq_of_lt hch]
        simp only [rowAcc, show ¬ k < i by omega_arith, show ¬ k < i + 14 by omega_arith, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r9, .r11]).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
        (by decide), h.rest.trans (hr6.mono (by decide)), ?_, hr11, ?_, ?_⟩, ?_⟩
    · rw [u6.other _ (by decide), u5.gpr, u4.gpr, e9', Offset.add_add, Nat.mul_succ]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [val32_congr hacc]; exact row_val h.val
    · rw [hr11, ofNat_ne_zero (by omega_arith)]

/-- The rows of doublewords: from `s`, the 28 limbs of `[x] · [y]` at `ACC`,
then `k`. -/
theorem rows64_ok {x y : Nat} (hx : x + 56 ≤ ACC) (hy : y + 56 ≤ ACC) (hx4 : x % 4 = 0)
    (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ s', Ctx b s' → Rest clob s s' → Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem s'.mem →
      val32 (accw ACC s'.mem b) 28 = V s.mem b x * V s.mem b y → WP isa rest s' Q) :
    WP isa (.seq (.block (zeroAcc ++ ([.addi .r9 .r6 0, .li .r11 7] : List Instr)))
      (.seq (.loop (.block (row64 x y)) (.nonzero .d .r11)) rest)) s Q := by
  have hA := ACC_eq
  have hpre : WP isa (.block (zeroAcc ++ ([.addi .r9 .r6 0, .li .r11 7] : List Instr))) s
      (RowInv64 b x y s 0) := by
    refine WP.append (zeroAcc_ok hc) fun s2 ⟨hz, hf2, hr2⟩ => ?_
    have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
    refine wp_addi (by decide) (by decide) fun s3 u3 => wp_li (by decide) fun s4 u4 => WP.block_nil ?_
    have hr : Rest clob s s4 :=
      (hr2.mono (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
    have hm4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
    refine ⟨hc.of_rest hr (by decide), hr, ?_, u4.gpr, ?_, ?_⟩
    · rw [u4.other _ (by decide), u3.gpr, hc2.r6]
    · rw [hm4]; exact hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
    · rw [hm4, Nat.zero_add, accW_val32, show (2 * 7 : Nat) = 14 from rfl,
        val32_congr (f := fun k => wd s2.mem b (ACC + 4 * k)) (g := fun _ => 0) (fun k hk => hz k hk),
        val32_zero_fn, show colsV (ew s.mem b x) 0 = 0 from rfl, Nat.zero_mul]
  refine WP.seq (WP.mono hpre fun s1 h1 => ?_)
  refine WP.seq (WP.mono (Q := RowInv64 b x y s 7) (WP.loop (M := isa)
    (fun n s' => ∃ i, n = 7 - i ∧ i < 7 ∧ RowInv64 b x y s i s') ?_ 7 s1 ⟨0, rfl, by decide, h1⟩)
    fun s2 h2 => ?_)
  · rintro n s' ⟨i, rfl, hi, hr⟩
    refine WP.mono (row64_ok hx hy hx4 hy4 hi hr) fun s'' ⟨hr', hz⟩ => ?_
    by_cases h7 : i + 1 = 7
    · refine .inl ⟨by rw [eval_nonzero, hz]; simp [h7], ?_⟩
      rw [h7] at hr'; exact hr'
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 7 - (i + 1), by omega_arith, i + 1, rfl,
        by omega_arith, hr'⟩
  · refine k s2 h2.ctx h2.rest h2.frame ?_
    have hv := h2.val
    rw [← V_eq_cols, ← V_eq_cols, accW_val32] at hv
    exact hv

/-! ## The reduction -/

/-- What `rotSrc k` adds: doubleword `k` of `h` rotated by 224 bits. -/
def rotW (h : Nat → Nat) (k : Nat) : Nat := h ((k + 3) % 7) / 2 ^ 32 + h ((k + 4) % 7) % 2 ^ 32 * 2 ^ 32

/-- What `hiSrc k` adds: doubleword `k` of `h` with its low 224 bits cleared. -/
def hiW (h : Nat → Nat) (k : Nat) : Nat :=
  if k < 3 then 0 else if k = 3 then h 3 / 2 ^ 32 * 2 ^ 32 else h k

/-- The low 224 bits of `colsV h 7`. -/
def loP (h : Nat → Nat) : Nat := h 0 + 2 ^ 64 * h 1 + 2 ^ 128 * h 2 + 2 ^ 192 * (h 3 % 2 ^ 32)

/-- `colsV h 7` above bit 224. -/
def hiP (h : Nat → Nat) : Nat := h 3 / 2 ^ 32 + 2 ^ 32 * h 4 + 2 ^ 96 * h 5 + 2 ^ 160 * h 6

theorem colsV_split (h : Nat → Nat) : colsV h 7 = loP h + 2 ^ 224 * hiP h := by
  have := Nat.mod_add_div (h 3) (2 ^ 32)
  simp only [colsV, loP, hiP]
  generalize h 3 % 2 ^ 32 = l at *
  generalize h 3 / 2 ^ 32 = a at *
  omega_arith

theorem colsV_rotW (h : Nat → Nat) : colsV (rotW h) 7 = hiP h + 2 ^ 224 * loP h := by
  have e0 := Nat.mod_add_div (h 0) (2 ^ 32); have e1 := Nat.mod_add_div (h 1) (2 ^ 32)
  have e2 := Nat.mod_add_div (h 2) (2 ^ 32); have e3 := Nat.mod_add_div (h 3) (2 ^ 32)
  have e4 := Nat.mod_add_div (h 4) (2 ^ 32); have e5 := Nat.mod_add_div (h 5) (2 ^ 32)
  have e6 := Nat.mod_add_div (h 6) (2 ^ 32)
  simp only [colsV, rotW, loP, hiP, Nat.reduceAdd, Nat.reduceMod]
  generalize h 0 % 2 ^ 32 = l0 at *; generalize h 0 / 2 ^ 32 = a0 at *
  generalize h 1 % 2 ^ 32 = l1 at *; generalize h 1 / 2 ^ 32 = a1 at *
  generalize h 2 % 2 ^ 32 = l2 at *; generalize h 2 / 2 ^ 32 = a2 at *
  generalize h 3 % 2 ^ 32 = l3 at *; generalize h 3 / 2 ^ 32 = a3 at *
  generalize h 4 % 2 ^ 32 = l4 at *; generalize h 4 / 2 ^ 32 = a4 at *
  generalize h 5 % 2 ^ 32 = l5 at *; generalize h 5 / 2 ^ 32 = a5 at *
  generalize h 6 % 2 ^ 32 = l6 at *; generalize h 6 / 2 ^ 32 = a6 at *
  omega_arith

theorem colsV_hiW (h : Nat → Nat) : colsV (hiW h) 7 = 2 ^ 224 * hiP h := by
  simp only [colsV, hiW, hiP, Nat.reduceLT, Nat.lt_irrefl, Nat.reduceEqDiff, ↓reduceIte]
  generalize h 3 / 2 ^ 32 = a
  omega_arith

theorem mul_mod_shift (c : Nat) : c * 2 ^ 32 % 2 ^ 64 = c % 2 ^ 32 * 2 ^ 32 :=
  Nat.mul_mod_mul_right (2 ^ 32) c (2 ^ 32)

/-- `rotSrc k`: doubleword `k` of the rotation of `m`'s high half into `r8`. -/
theorem rotSrc_ok {m : Mem} {k : Nat} {t : State} (hc : Ctx b t)
    (hm : ∀ j < 7, dw t.mem b (ACC + 56 + 8 * j) = dw m b (ACC + 56 + 8 * j)) :
    WP isa (.block (rotSrc k)) t fun t' =>
      (t'.gpr .r8).toNat = rotW (ew m b (ACC + 56)) k ∧ Rest [.r5, .r8, .r10] t t' ∧
        t'.mem = t.mem ∧ t'.ca = t.ca := by
  have hA := ACC_eq
  have h3 : (k + 3) % 7 < 7 := Nat.mod_lt _ (by decide)
  have h4 : (k + 4) % 7 < 7 := Nat.mod_lt _ (by decide)
  unfold rotSrc
  refine ldw_ok hc (by omega) (by omega) ?_
  refine ldw_ok (hc.of_rest ((Upd.write _ _ _).rest (ws := [.r5]) (by simp)) (by decide))
    (by omega) (by omega) ?_
  refine WP.cons (exec_lsr_d (by decide)) (WP.cons (exec_lsl (by decide))
    (WP.cons exec_add (WP.block_nil ⟨?_, ?_, rfl, rfl⟩)))
  · simp only [RegUpd.gpr_write_self, reduceCtorEq, not_false_eq_true,
      RegUpd.gpr_write_of_ne, RegUpd.mem_write]
    have ea : (t.mem.readW (b + BitVec.ofNat 64 (ACC + 56 + 8 * ((k + 3) % 7))) 64).toNat =
        ew m b (ACC + 56) ((k + 3) % 7) := hm _ h3
    have ec : (t.mem.readW (b + BitVec.ofNat 64 (ACC + 56 + 8 * ((k + 4) % 7))) 64).toNat =
        ew m b (ACC + 56) ((k + 4) % 7) := hm _ h4
    have la := dw_lt m b (ACC + 56 + 8 * ((k + 3) % 7))
    have lc := Nat.mod_lt (ew m b (ACC + 56) ((k + 4) % 7)) (show 0 < 2 ^ 32 by decide)
    have da : ew m b (ACC + 56) ((k + 3) % 7) / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    rw [toNat_add_lt (by rw [toNat_shr, toNat_shl, ea, ec, mul_mod_shift]; omega_arith), toNat_shr,
      toNat_shl, ea, ec, mul_mod_shift, rotW]
  · exact ((Upd.write _ _ _).rest (by simp)).trans (((Upd.write _ _ _).rest (by simp)).trans
      (((Upd.write _ _ _).rest (by simp)).trans (((Upd.write _ _ _).rest (by simp)).trans
        ((Upd.write _ _ _).rest (by simp)))))

/-- `hiSrc k`: doubleword `k ≥ 3` of `m`'s high half, its low 224 bits cleared, into `r8`. -/
theorem hiSrc_ok {m : Mem} {k : Nat} (hk3 : 3 ≤ k) (hk : k < 7) {t : State} (hc : Ctx b t)
    (hm : ∀ j < 7, dw t.mem b (ACC + 56 + 8 * j) = dw m b (ACC + 56 + 8 * j)) :
    WP isa (.block (hiSrc k)) t fun t' =>
      (t'.gpr .r8).toNat = hiW (ew m b (ACC + 56)) k ∧ Rest [.r5, .r8, .r10] t t' ∧
        t'.mem = t.mem ∧ t'.ca = t.ca := by
  have hA := ACC_eq
  have hn : ¬ k < 3 := by omega
  unfold hiSrc
  by_cases e3 : k = 3
  · subst e3
    simp only [↓reduceIte]
    refine ldw_ok hc (by omega) (by omega) ?_
    refine WP.cons (exec_lsr_d (by decide)) (WP.cons (exec_lsl (by decide))
      (WP.block_nil ⟨?_, ?_, rfl, rfl⟩))
    · have ea : (t.mem.readW (b + BitVec.ofNat 64 (ACC + 56 + 24)) 64).toNat = ew m b (ACC + 56) 3 :=
        hm 3 (by decide)
      have la := dw_lt m b (ACC + 56 + 8 * 3)
      have da : ew m b (ACC + 56) 3 / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
      simp only [RegUpd.gpr_write_self]
      rw [toNat_shl, toNat_shr, ea, Nat.mod_eq_of_lt (by omega_arith)]
      simp only [hiW, hn, ↓reduceIte]
    · exact ((Upd.write _ _ _).rest (by simp)).trans (((Upd.write _ _ _).rest (by simp)).trans
        ((Upd.write _ _ _).rest (by simp)))
  · simp only [e3, ↓reduceIte]
    refine ldw_ok hc (by omega) (by omega) (WP.block_nil ⟨?_, (Upd.write _ _ _).rest (by simp), rfl, rfl⟩)
    simp only [RegUpd.gpr_write_self, hiW, hn, e3, ↓reduceIte]
    exact hm k hk

/-- Step `k` of a chain adding the words `src` leaves in `r8` into `[o]`. -/
theorem accStep_ok {src : Nat → List Instr} {W : Nat → Nat} {o : Nat} (ho : o + 56 ≤ 4096)
    (ho4 : o % 4 = 0) {s0 : State} {k : Nat} (hk : k < 7) {s : State}
    (h : CInv (b := b) [.r5, .r7, .r8, .r10] false o (ew s0.mem b o) W s0 k s)
    (hsrc : ∀ t, Ctx b t → Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s0.mem t.mem →
      WP isa (.block (src k)) t fun t' => (t'.gpr .r8).toNat = W k ∧ Rest [.r5, .r8, .r10] t t' ∧
        t'.mem = t.mem ∧ t'.ca = t.ca) :
    WP isa (.block (accStep src o k)) s
      (CInv (b := b) [.r5, .r7, .r8, .r10] false o (ew s0.mem b o) W s0 (k + 1)) := by
  have hc := h.ctx
  have eX : dw s.mem b (o + 8 * k) = dw s0.mem b (o + 8 * k) := dw_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  unfold accStep
  refine ldw_ok hc (by omega) (by omega) ?_
  generalize hs1 : s.write .r7 (s.mem.readW (b + BitVec.ofNat 64 (o + 8 * k)) 64) = s1
  have r1 : Rest [.r5, .r7, .r8, .r10] s s1 := by rw [← hs1]; exact (Upd.write _ _ _).rest (by simp)
  have hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  have m1 : s1.mem = s.mem := by rw [← hs1, RegUpd.mem_write]
  have c1 : s1.ca = s.ca := by rw [← hs1, RegUpd.ca_write]
  have g7 : (s1.gpr .r7).toNat = dw s0.mem b (o + 8 * k) := by
    rw [← hs1, RegUpd.gpr_write_self, ← eX]; rfl
  have hf1 : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s0.mem s1.mem := by
    rw [m1]; exact h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩
  refine WP.append (hsrc s1 hc1 hf1) fun s2 ⟨g8, r2, m2, c2⟩ => ?_
  have g7' : s2.gpr .r7 = s1.gpr .r7 := r2.gpr _ (by decide)
  refine chainOp_ok false k .r8 fun t u => ?_
  have r2' : Rest [.r5, .r7, .r8, .r10] s1 t := (r2.mono (by decide)).trans (u.rest (by simp))
  refine cstore_ok hk ho ho4 h (hc1.of_rest r2' (by decide)) (r1.trans r2') (by rw [u.mem, m2, m1]) ?_
  rw [u.val, g7', g7, g8, c2, c1]

/-- `[o]`'s doublewords unchanged since `m`, outside `[o]`. -/
theorem dw_hi {o : Nat} (ho : o + 56 ≤ ACC) {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] m m')
    {j : Nat} (hj : j < 7) : dw m' b (ACC + 56 + 8 * j) = dw m b (ACC + 56 + 8 * j) :=
  dw_frame hf fun r hr => by
    have hA := ACC_eq
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- `sums o`: `[o]` and the carry `c` in `r4` hold `L + H + rot(H) + 2²²⁴ Hₕ`, for
the product `L + 2⁴⁴⁸ H` at `ACC`. -/
theorem sums_ok {o : Nat} (ho : o + 56 ≤ ACC) (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (sums o)) s fun s' =>
      Ctx b s' ∧ Rest [.r4, .r5, .r7, .r8, .r10] s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      (s'.gpr .r4).toNat ≤ 3 ∧ (s'.gpr .r5).toNat = 2 ^ 32 * (s'.gpr .r4).toNat ∧
      (s'.gpr .r8).toNat = 0 ∧
      colsV (ew s'.mem b o) 7 + (2 ^ 64) ^ 7 * (s'.gpr .r4).toNat =
        colsV (ew s.mem b ACC) 7 + loP (ew s.mem b (ACC + 56)) + 2 ^ 224 * hiP (ew s.mem b (ACC + 56)) +
          (hiP (ew s.mem b (ACC + 56)) + 2 ^ 224 * loP (ew s.mem b (ACC + 56))) +
          2 ^ 224 * hiP (ew s.mem b (ACC + 56)) := by
  have hA := ACC_eq
  have ho' : o + 56 ≤ 4096 := by omega
  unfold sums
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `L + H`
  refine WP.append (chainRun_ok (sub := false) (x := ACC) (y := ACC + 56) ho' (by omega) (by omega)
    ho4 (by omega) (by omega) (by omega) (by omega) hc) fun s1 h1 => ?_
  have hc1 := h1.ctx
  refine WP.cons (exec_li (by decide)) (wp_addze fun s2 u2 => ?_)
  have v2 := u2.val
  rw [RegUpd.gpr_write_self, RegUpd.ca_write] at v2
  have z : (BitVec.ofNat 64 0).toNat = 0 := rfl
  rw [z] at v2
  have r2 : Rest [.r4] s1 s2 := ((Upd.write _ _ _).rest (by simp)).trans (u2.rest (by simp))
  have hc2 : Ctx b s2 := hc1.of_rest r2 (by decide)
  have m2 : s2.mem = s1.mem := by rw [u2.mem, RegUpd.mem_write]
  have hf2 : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s2.mem := by rw [m2]; exact h1.frame
  -- `+ rot(H)`
  refine WP.append (wp_range_flatMap (M := isa) (N := 7)
    (CInv (b := b) [.r5, .r7, .r8, .r10] false o (ew s2.mem b o) (rotW (ew s.mem b (ACC + 56))) s2)
    (fun _ _ hk ht => accStep_ok ho' ho4 hk ht fun t hct hft => rotSrc_ok hct fun j hj =>
      dw_hi ho (hf2.trans hft) hj) 7 (Nat.le_refl _) s2 (CInv.start hc2)) fun s3 h3 => ?_
  refine wp_addze fun s4 u4 => ?_
  have hc3 := h3.ctx
  have r4 : Rest [.r4] s3 s4 := u4.rest (by simp)
  have hc4 : Ctx b s4 := hc3.of_rest r4 (by decide)
  have g4 : s3.gpr .r4 = s2.gpr .r4 := h3.rest.gpr _ (by decide)
  have v4 := u4.val
  rw [g4] at v4
  have l4 := (s4.gpr .r4).isLt
  have ca1 : s1.ca.toNat ≤ 1 := Bool.toNat_le _
  have ca3 : s3.ca.toNat ≤ 1 := Bool.toNat_le _
  have l2 := (s2.gpr .r4).isLt
  have z4 : s4.ca.toNat = 0 := by omega
  have hf4 : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s4.mem := by
    rw [u4.mem]; exact hf2.trans h3.frame
  -- `+ 2²²⁴ Hₕ`
  refine WP.append (wp_range_flatMap (M := isa) (N := 4)
    (fun j => CInv (b := b) [.r5, .r7, .r8, .r10] false o (ew s4.mem b o) (hiW (ew s.mem b (ACC + 56))) s4
      (j + 3))
    (fun j t hj ht => by
      rw [show j + 1 + 3 = j + 3 + 1 by omega]
      exact accStep_ok ho' ho4 (by omega) ht fun t' hct hft => hiSrc_ok (by omega) (by omega) hct
        fun i hi => dw_hi ho (hf4.trans hft) hi) 4 (Nat.le_refl _) s4
    ⟨hc4, Rest.refl _ _, Frame.refl _ _, fun _ => by
      simp only [z4, Nat.mul_zero, Nat.add_zero, Nat.zero_add, colsV, cvD, hiW, Nat.reduceLT, ↓reduceIte,
        Bool.false_eq_true, Nat.mul_zero]⟩) fun s5 h5 => ?_
  refine wp_addze fun s6 u6 => wp_lsl (by decide) fun s7 u7 => wp_li (by decide) fun s8 u8 => ?_
  have hc5 := h5.ctx
  have r8 : Rest [.r4, .r5, .r8] s5 s8 :=
    (u6.rest (by simp)).trans ((u7.rest (by simp)).trans (u8.rest (by simp)))
  have m8 : s8.mem = s5.mem := by rw [u8.mem, u7.mem, u6.mem]
  have g5 : s5.gpr .r4 = s4.gpr .r4 := h5.rest.gpr _ (by decide)
  have v6 := u6.val
  rw [g5] at v6
  have ca5 : s5.ca.toNat ≤ 1 := Bool.toNat_le _
  have e6 : (s6.gpr .r4).toNat = (s4.gpr .r4).toNat + s5.ca.toNat := by
    have : s6.ca.toNat ≤ 1 := Bool.toNat_le _
    omega
  have f4 : (s8.gpr .r4).toNat = s1.ca.toNat + s3.ca.toNat + s5.ca.toNat := by
    rw [u8.other _ (by decide), u7.other _ (by decide), e6]; omega
  have f5 : (s8.gpr .r5).toNat = 2 ^ 32 * (s8.gpr .r4).toNat := by
    rw [u8.other _ (by decide), u7.gpr, toNat_shl, f4, e6, Nat.mod_eq_of_lt (by omega)]; omega
  refine WP.block_nil ⟨hc5.of_rest r8 (by decide), ?_, ?_, by omega, f5, by rw [u8.gpr]; rfl, ?_⟩
  · exact (h1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans ((h3.rest.mono (by decide)).trans
      ((r4.mono (by decide)).trans ((h5.rest.mono (by decide)).trans (r8.mono (by decide))))))
  · rw [m8]; exact hf4.trans h5.frame
  · have v1 : colsV (ew s1.mem b o) 7 + (2 ^ 64) ^ 7 * s1.ca.toNat =
        colsV (ew s.mem b ACC) 7 + colsV (fun j => cvD false (ew s.mem b (ACC + 56) j)) 7 + 0 :=
      h1.val (by decide)
    have v3 : colsV (ew s3.mem b o) 7 + (2 ^ 64) ^ 7 * s3.ca.toNat =
        colsV (ew s2.mem b o) 7 + colsV (fun j => cvD false (rotW (ew s.mem b (ACC + 56)) j)) 7 + 0 :=
      h3.val (by decide)
    have v5 : colsV (ew s5.mem b o) 7 + (2 ^ 64) ^ 7 * s5.ca.toNat =
        colsV (ew s4.mem b o) 7 + colsV (fun j => cvD false (hiW (ew s.mem b (ACC + 56)) j)) 7 + 0 :=
      h5.val (by decide)
    rw [colsV_cvD_false, colsV_split (ew s.mem b (ACC + 56))] at v1
    rw [colsV_cvD_false, colsV_rotW, m2] at v3
    rw [colsV_cvD_false, colsV_hiW, u4.mem] at v5
    rw [m8, f4]
    generalize colsV (ew s.mem b ACC) 7 = L at *
    generalize loP (ew s.mem b (ACC + 56)) = Lo at *
    generalize hiP (ew s.mem b (ACC + 56)) = Hi at *
    generalize (2 ^ 64) ^ 7 = K at *
    generalize s1.ca.toNat = c1 at *
    generalize s3.ca.toNat = c3 at *
    generalize s5.ca.toNat = c5 at *
    generalize colsV (ew s1.mem b o) 7 = S1 at *
    generalize colsV (ew s3.mem b o) 7 = S3 at *
    generalize colsV (ew s5.mem b o) 7 = S5 at *
    rw [Nat.mul_add, Nat.mul_add]
    omega

/-- The value of the reduction: the sums `S + 2⁴⁴⁸ c` of `sums`, folded twice, are
congruent to the product. -/
theorem reduce_arith {L Lo Hi S c S9 c9 S11 c11 : Nat} (hc : c ≤ 3) (hS : S < 2 ^ 224 * 2 ^ 224)
    (hS9 : S9 < 2 ^ 224 * 2 ^ 224) (h11 : c11 ≤ 1)
    (v : S + (2 ^ 64) ^ 7 * c = L + Lo + 2 ^ 224 * Hi + (Hi + 2 ^ 224 * Lo) + 2 ^ 224 * Hi)
    (v9 : S9 + (2 ^ 64) ^ 7 * c9 = S + (c + 2 ^ 224 * c) + 0)
    (v11 : S11 + (2 ^ 64) ^ 7 * c11 = S9 + (c9 + 2 ^ 224 * c9) + 0) :
    S11 % P = (L + (2 ^ 64) ^ 7 * (Lo + 2 ^ 224 * Hi)) % P := by
  have z : c11 = 0 := by omega
  have key : S11 + (2 ^ 224 * 2 ^ 224 - 2 ^ 224 - 1) * (c + c9 + Lo + (2 ^ 224 + 1) * Hi) =
      L + (2 ^ 64) ^ 7 * (Lo + 2 ^ 224 * Hi) := by
    omega
  rw [P_eq, ← key, Nat.add_mul_mod_self_left]

theorem accW_cols (m : Mem) (a : Nat) : accW a m b 7 = colsV (ew m b a) 7 := by
  simp only [accW, colsV]

/-- `reduce o`: `[o]` congruent to the product of fourteen doublewords at `ACC`. -/
theorem reduce_ok {o : Nat} (ho : o + 56 ≤ ACC) (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (reduce o)) s fun s' =>
      Rest [.r4, .r5, .r7, .r8, .r10] s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      V s'.mem b o % P = accW ACC s.mem b 14 % P := by
  have hA := ACC_eq
  have ho' : o + 56 ≤ 4096 := by omega
  unfold reduce
  simp only [List.append_assoc]
  refine WP.append (sums_ok ho ho4 hc) fun s1 ⟨hc1, r1, f1, l4, e5, e8, v1⟩ => ?_
  refine WP.append (foldRun_ok (sub := false) ho' ho4 hc1) fun s9 h9 => ?_
  refine carryPrep_ok h9.ctx fun s10 hc10 r10 m10 e4' e5' e8' => ?_
  refine WP.mono (foldRun_ok (sub := false) ho' ho4 hc10) fun s11 h11 => ⟨?_, ?_, ?_⟩
  · exact r1.trans ((h9.rest.mono (by decide)).trans ((r10.mono (by decide)).trans
      (h11.rest.mono (by decide))))
  · have f11 := h11.frame
    rw [m10] at f11
    exact f1.trans (h9.frame.trans f11)
  · have v9 : colsV (ew s9.mem b o) 7 + (2 ^ 64) ^ 7 * s9.ca.toNat =
        colsV (ew s1.mem b o) 7 + colsV (fun j => cvD false ((s1.gpr (foldSrc64 j)).toNat)) 7 + 0 :=
      h9.val (by decide)
    have v11 : colsV (ew s11.mem b o) 7 + (2 ^ 64) ^ 7 * s11.ca.toNat =
        colsV (ew s10.mem b o) 7 + colsV (fun j => cvD false ((s10.gpr (foldSrc64 j)).toNat)) 7 + 0 :=
      h11.val (by decide)
    rw [colsV_cvD_false, foldW_val s1 rfl e5 e8] at v9
    rw [colsV_cvD_false, foldW_val s10 e4' e5' e8', m10] at v11
    have e := accW_add ACC s.mem b 7 7
    rw [show 7 + 7 = 14 from rfl] at e
    rw [V_eq_cols, e, accW_cols, accW_cols, show ACC + 8 * 7 = ACC + 56 from rfl,
      colsV_split (ew s.mem b (ACC + 56))]
    exact reduce_arith l4 (V_cols_lt s1.mem o) (V_cols_lt s9.mem o) (Bool.toNat_le _) v1 v9 v11

theorem mul_ok {o x y : Nat} (ho : o + 56 ≤ ACC) (hx : x + 56 ≤ ACC)
    (hy : y + 56 ≤ ACC) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) (ho4 : o % 4 = 0) {s : State}
    (hc : Ctx b s) :
    WP isa (mul o x y) s fun s' =>
      Rest clob s s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := by
  unfold mul
  refine rows64_ok hx hy hx4 hy4 hc fun s2 h2ctx h2rest h2frame h2val => ?_
  refine WP.mono (reduce_ok ho ho4 h2ctx) fun s3 ⟨hr3, hf3, hv3⟩ =>
    ⟨h2rest.trans (hr3.mono (by decide)), ?_, ?_⟩
  · have hf2 : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩]
        s.mem s2.mem := h2frame.mono fun r hr => by simp [List.mem_singleton.mp hr]
    exact hf2.trans (hf3.mono fun r hr => by simp [List.mem_singleton.mp hr])
  · rw [hv3, accW_val32]
    exact congrArg (· % P) h2val


/-! ## Stores and loads at offsets of the working space -/

open VG.PPC64LE.Spill (saveMem Saved Fits saveMem_saved saveMem_frame_base)

/-- `stdsAt base l`: the memory is `saveMem` of the registers of `l`, from `b + base`. -/
theorem stdsAt_ok {base : Nat} {l : List (Reg × Nat)} (h4 : base % 4 = 0)
    (hl : ∀ p ∈ l, p.2 % 4 = 0 ∧ base + p.2 + 8 ≤ 4096) {s : State} (hc : Ctx b s)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (b + BitVec.ofNat 64 base) s.gpr l → WP isa (.block rest) s' Q) :
    WP isa (.block (stdsAt base l ++ rest)) s Q := by
  induction l generalizing s with
  | nil => exact k s rfl rfl rfl rfl rfl
  | cons p l ih =>
    obtain ⟨r, d⟩ := p
    have hd := hl (r, d) List.mem_cons_self
    simp only [stdsAt, List.map_cons, List.cons_append]
    refine sd0_ok hc (d := base + d) (by omega) (by omega) fun s1 u1 => ?_
    have hc1 : Ctx b s1 := ⟨by rw [u1.gpr]; exact hc.r6, by rw [u1.wr]; exact hc.wr⟩
    refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hc1 fun s' g' rd' wr' sp' m' => ?_
    refine k s' (g'.trans u1.gpr) (rd'.trans u1.rd) (wr'.trans u1.wr) (sp'.trans u1.sp) ?_
    rw [m', u1.mem, u1.gpr, saveMem, Offset.add_add]

/-- `ldsAt base l`: each register of `l` (distinct, none `r6`) holds its
doubleword from `b + base`. -/
theorem ldsAt_ok {base : Nat} {l : List (Reg × Nat)} (h4 : base % 4 = 0)
    (hl : ∀ p ∈ l, p.2 % 4 = 0 ∧ base + p.2 + 8 ≤ 4096) (hr : (l.map Prod.fst).Nodup)
    (h6 : ∀ p ∈ l, p.1 ≠ .r6) {s : State} (hc : Ctx b s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx b s' → Rest (l.map Prod.fst) s s' → s'.mem = s.mem →
      (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (b + BitVec.ofNat 64 base + BitVec.ofNat 64 p.2) 64) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (ldsAt base l ++ rest)) s Q := by
  induction l generalizing s with
  | nil => exact k s hc (Rest.refl _ _) rfl fun _ h => absurd h List.not_mem_nil
  | cons p l ih =>
    obtain ⟨r, d⟩ := p
    have hd := hl (r, d) List.mem_cons_self
    have hnd := List.nodup_cons.mp hr
    have hr6 : r ≠ .r6 := h6 (r, d) List.mem_cons_self
    simp only [ldsAt, List.map_cons, List.cons_append]
    refine ld0_ok hc (d := base + d) (by omega) (by omega) fun s1 u1 => ?_
    have hr1 : Rest ((r, d) :: l |>.map Prod.fst) s s1 := u1.rest List.mem_cons_self
    have hc1 : Ctx b s1 := hc.of_rest hr1 (by
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨Ne.symm hr6, fun hm => by
        obtain ⟨q, hq, e⟩ := List.mem_map.mp hm
        exact h6 q (List.mem_cons_of_mem _ hq) e⟩)
    refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hnd.2
      (fun q hq => h6 q (List.mem_cons_of_mem _ hq)) hc1 fun s' c' r' m' v' => ?_
    refine k s' c' (hr1.trans (r'.mono fun x hx => List.mem_cons_of_mem _ hx)) (m'.trans u1.mem)
      fun q hq => ?_
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [r'.gpr _ hnd.1, u1.gpr, Offset.add_add]
    · rw [v' q hq, u1.mem]

/-! ## The carry chains of the reduction -/

/-- After `n` steps of `chain7 src` from `s0` (`src` apart from `pw 0`, …,
`pw 6`): `pw 0`, …, `pw (n - 1)` and CA hold `pw_{<n} + src_{<n}`. -/
theorem chainN_ok {src : Nat → Reg} (hs : ∀ k < 7, ∀ j < 7, src k ≠ pw j) {s0 : State} :
    ∀ n ≤ 7, WP isa (.block ((List.range n).map fun k => chainR k (src k))) s0 fun s =>
      colsV (fun j => (s.gpr (pw j)).toNat) n + (2 ^ 64) ^ n * (if n = 0 then 0 else s.ca.toNat) =
        colsV (fun j => (s0.gpr (pw j)).toNat) n + colsV (fun j => (s0.gpr (src j)).toNat) n ∧
      Rest clobR s0 s ∧ (∀ r, (∀ j < n, r ≠ pw j) → s.gpr r = s0.gpr r) ∧ s.mem = s0.mem
  | 0, _ => WP.block_nil ⟨by simp [colsV], Rest.refl _ _, fun _ _ => rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.append (chainN_ok hs n (by omega)) fun s1 ⟨v1, r1, k1, m1⟩ => ?_
    have hpn : ∀ j < n, pw n ≠ pw j := fun j hj e => by have := pw_inj _ (by omega) _ (by omega) e; omega
    have e0 : s1.gpr (pw n) = s0.gpr (pw n) := k1 _ hpn
    have es : s1.gpr (src n) = s0.gpr (src n) := k1 _ fun j hj => hs n (by omega) j (by omega)
    have hpc : pw n ∈ clobR := (pw_facts n (by omega)).2.2.2
    have fin : ∀ (s2 : State), UpdC s1 s2 (pw n) ((s1.gpr (pw n)).toNat + (s1.gpr (src n)).toNat +
        (if n = 0 then 0 else s1.ca.toNat)) → WP isa (.block []) s2 fun s =>
        colsV (fun j => (s.gpr (pw j)).toNat) (n + 1) + (2 ^ 64) ^ (n + 1) *
          (if n + 1 = 0 then 0 else s.ca.toNat) =
          colsV (fun j => (s0.gpr (pw j)).toNat) (n + 1) + colsV (fun j => (s0.gpr (src j)).toNat) (n + 1) ∧
        Rest clobR s0 s ∧ (∀ r, (∀ j < n + 1, r ≠ pw j) → s.gpr r = s0.gpr r) ∧ s.mem = s0.mem := by
      intro s2 u2
      refine WP.block_nil ⟨?_, r1.trans (u2.rest hpc), fun r hr => ?_, u2.mem.trans m1⟩
      · have hlow : colsV (fun j => (s2.gpr (pw j)).toNat) n = colsV (fun j => (s1.gpr (pw j)).toNat) n :=
          colsV_congr fun j hj => by rw [u2.other _ (Ne.symm (hpn j hj))]
        have v2 := u2.val
        rw [e0, es] at v2
        have h2 := congrArg ((2 ^ 64) ^ n * ·) v2
        simp only [Nat.mul_add] at h2
        rw [colsV, colsV, colsV, hlow, show (2 ^ 64) ^ (n + 1) = (2 ^ 64) ^ n * 2 ^ 64 from Nat.pow_succ _ _,
          Nat.mul_assoc]
        simp only [Nat.add_one_ne_zero, ↓reduceIte]
        generalize (2 ^ 64) ^ n = K at *
        omega
      · rw [u2.other _ (hr n (by omega)), k1 _ fun j hj => hr j (by omega)]
    by_cases h0 : n = 0
    · subst h0
      simp only [chainR, ↓reduceIte]
      exact wp_addc fun s2 u2 => fin s2 (by simpa using u2)
    · simp only [chainR, h0, ↓reduceIte]
      exact wp_adde fun s2 u2 => fin s2 (by simpa [h0] using u2)

/-! ## The reduction in registers -/

theorem rot_facts : ∀ k < 7, rotReg k ≠ .r18 ∧ rotReg k ≠ .r4 ∧ rotReg k ∈ clobR ∧
    (∀ j < 14, rotReg k ≠ pw j) ∧ (∀ j < 7, j ≠ k → rotReg k ≠ rotReg j) := by decide

theorem pw_ne : ∀ j < 14, pw j ≠ .r18 ∧ pw j ≠ .r19 ∧ pw j ≠ .r20 := by decide

theorem hiReg_ne : ∀ k < 7, ∀ j < 7, hiReg k ≠ pw j := by decide

theorem foldReg_ne : ∀ k < 7, ∀ j < 7, foldReg k ≠ pw j := by decide

theorem hi_ne : ∀ k < 7, ∀ j < 7, pw (7 + k) ≠ pw j := by decide

/-- After `n` steps of the rotation from `s0`: `rotReg j` (`j < n`) holds
doubleword `j` of the high half `pw 7`, …, `pw 13` rotated by 224 bits. -/
theorem rotsN_ok {s0 : State} : ∀ n ≤ 7, WP isa (.block ((List.range n).flatMap rotR)) s0 fun s =>
    Rest clobR s0 s ∧ s.mem = s0.mem ∧ (∀ r, r ≠ .r18 → (∀ j < n, r ≠ rotReg j) → s.gpr r = s0.gpr r) ∧
    ∀ j < n, (s.gpr (rotReg j)).toNat = rotW (fun i => (s0.gpr (pw (7 + i))).toNat) j
  | 0, _ => WP.block_nil ⟨Rest.refl _ _, rfl, fun _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (rotsN_ok n (by omega)) fun s1 ⟨r1, m1, k1, v1⟩ => ?_
    obtain ⟨t27, -, tc, tpw, ttr⟩ := rot_facts n (by omega)
    have kpw : ∀ i < 14, s1.gpr (pw i) = s0.gpr (pw i) := fun i hi =>
      k1 _ (pw_ne i hi).1 fun j hj e => (rot_facts j (by omega)).2.2.2.1 i hi e.symm
    simp only [rotR]
    refine wp_lsr (by decide) fun s2 u2 => wp_lsl (by decide) fun s3 u3 => wp_add fun s4 u4 => WP.block_nil ?_
    have hx : s2.gpr (rotReg n) = s0.gpr (pw (7 + (n + 3) % 7)) >>> 32 := by
      rw [u2.gpr, kpw _ (by omega)]
    have hy : s3.gpr .r18 = s0.gpr (pw (7 + (n + 4) % 7)) <<< 32 := by
      rw [u3.gpr, u2.other _ (tpw _ (by omega)).symm, kpw _ (by omega)]
    have hv : (s4.gpr (rotReg n)).toNat = rotW (fun i => (s0.gpr (pw (7 + i))).toNat) n := by
      rw [u4.gpr, u3.other _ t27, hx, hy]
      have l1 : (s0.gpr (pw (7 + (n + 3) % 7)) >>> 32).toNat < 2 ^ 32 := by
        rw [toNat_shr]; have := (s0.gpr (pw (7 + (n + 3) % 7))).isLt; omega
      have l2 : (s0.gpr (pw (7 + (n + 4) % 7)) <<< 32).toNat =
          (s0.gpr (pw (7 + (n + 4) % 7))).toNat % 2 ^ 32 * 2 ^ 32 := by
        rw [toNat_shl, mul_mod_shift]
      have l3 : (s0.gpr (pw (7 + (n + 4) % 7))).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
      rw [toNat_add_lt (by rw [l2]; omega_arith), toNat_shr, l2]; rfl
    refine ⟨r1.trans ((u2.rest tc).trans ((u3.rest (by decide)).trans (u4.rest tc))),
      by rw [u4.mem, u3.mem, u2.mem, m1], fun r h27 hr => ?_, fun j hj => ?_⟩
    · have hn' : r ≠ rotReg n := hr n (by omega)
      rw [u4.other _ hn', u3.other _ h27, u2.other _ hn', k1 _ h27 fun j hj => hr j (by omega)]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hne : rotReg j ≠ rotReg n := fun e => ttr j (by omega) (by omega) e.symm
        rw [u4.other _ hne, u3.other _ (rot_facts j (by omega)).1, u2.other _ hne, v1 j hj]
      · exact hv

/-- `li r4, 0; addze r4, r4`: the carry into `r4`. -/
theorem capture_ok {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Rest [.r4] s t → t.mem = s.mem → (t.gpr .r4).toNat = s.ca.toNat → WP isa (.block is) t Q) :
    WP isa (.block (.li .r4 0 :: .addze .r4 .r4 :: is)) s Q := by
  refine WP.cons (exec_li (by decide)) (wp_addze fun s2 u2 => ?_)
  have v2 := u2.val
  rw [RegUpd.gpr_write_self, RegUpd.ca_write] at v2
  have z : (BitVec.ofNat 64 0).toNat = 0 := rfl
  rw [z] at v2
  have c0 : s.ca.toNat ≤ 1 := Bool.toNat_le _
  have l2 := (s2.gpr .r4).isLt
  exact k s2 (((Upd.write _ _ _).rest (by simp)).trans (u2.rest (by simp)))
    (by rw [u2.mem, RegUpd.mem_write]) (by omega)

/-- The doublewords of a product of fourteen, split at seven. -/
theorem colsV_14 (f : Nat → Nat) : colsV f 14 = colsV f 7 + (2 ^ 64) ^ 7 * colsV (fun k => f (7 + k)) 7 := by
  simp only [colsV, Nat.reducePow, Nat.reduceAdd]
  omega

/-- `reduceR`: `pw 0`, …, `pw 6` congruent to the product in `pw`. -/
theorem reduceR_ok {s : State} (hc : Ctx b s) :
    WP isa (.block reduceR) s fun s' => Ctx b s' ∧ Rest clobR s s' ∧ s'.mem = s.mem ∧
      colsV (fun j => (s'.gpr (pw j)).toNat) 7 % P = pwSum s 14 % P := by
  have hpw7 : ∀ i < 7, pw (7 + i) ∈ clobR := fun i hi => (pw_facts (7 + i) (by omega)).2.2.2
  generalize hH : (fun i => (s.gpr (pw (7 + i))).toNat) = H
  unfold reduceR
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `L + H`.
  refine WP.append (chainN_ok (src := fun k => pw (7 + k)) (fun k hk j hj => hi_ne k hk j hj) 7
    (Nat.le_refl _)) fun s1 ⟨v1, r1, k1, m1⟩ => ?_
  simp only [↓reduceIte, show (7 : Nat) ≠ 0 from by decide] at v1
  have kH1 : ∀ i < 7, s1.gpr (pw (7 + i)) = s.gpr (pw (7 + i)) := fun i hi =>
    k1 _ fun j hj => hi_ne i hi j hj
  refine capture_ok fun s2 r2 m2 e2 => ?_
  have kH2 : ∀ i < 7, s2.gpr (pw (7 + i)) = s.gpr (pw (7 + i)) := fun i hi => by
    rw [r2.gpr _ (by simp; exact (pw_facts _ (by omega)).1), kH1 i hi]
  -- `+= 2²²⁴ Hₗ + Hₕ`.
  refine WP.append (rotsN_ok 7 (Nat.le_refl _)) fun s3 ⟨r3, m3, k3, v3⟩ => ?_
  have kp3 : ∀ i < 14, s3.gpr (pw i) = s2.gpr (pw i) := fun i hi =>
    k3 _ (pw_ne i hi).1 fun j hj e => (rot_facts j hj).2.2.2.1 i hi e.symm
  have e43 : s3.gpr .r4 = s2.gpr .r4 := k3 _ (by decide) fun j hj e => (rot_facts j hj).2.1 e.symm
  refine WP.append (chainN_ok (src := rotReg) (fun k hk j hj => (rot_facts k hk).2.2.2.1 j (by omega)) 7
    (Nat.le_refl _)) fun s4 ⟨v4, r4, k4, m4⟩ => ?_
  simp only [show (7 : Nat) ≠ 0 from by decide, ↓reduceIte] at v4
  have e44 : s4.gpr .r4 = s3.gpr .r4 := k4 _ fun j hj e => (pw_facts j (by omega)).1 e.symm
  refine wp_addze fun s5 u5 => ?_
  -- `+= 2²²⁴ Hₕ`.
  refine wp_li (by decide) fun s6 u6 => wp_lsr (by decide) fun s7 u7 => wp_lsl (by decide) fun s8 u8 => ?_
  have c1 : s1.ca.toNat ≤ 1 := Bool.toNat_le _
  have c4 : s4.ca.toNat ≤ 1 := Bool.toNat_le _
  have e5 : (s5.gpr .r4).toNat = s1.ca.toNat + s4.ca.toNat := by
    have := u5.val; have := u5.ca; have := (s5.gpr .r4).isLt
    rw [e44, e43, ← e2] at *; omega
  have k6 : ∀ i < 14, s6.gpr (pw i) = s4.gpr (pw i) := fun i hi => by
    rw [u6.other _ (pw_ne i hi).2.1, u5.other _ (pw_facts i (by omega)).1]
  have k8 : ∀ i < 14, s8.gpr (pw i) = s4.gpr (pw i) := fun i hi => by
    rw [u8.other _ (pw_ne i hi).2.2, u7.other _ (pw_ne i hi).2.2, k6 i hi]
  have kH4 : ∀ i < 7, s4.gpr (pw (7 + i)) = s.gpr (pw (7 + i)) := fun i hi => by
    rw [k4 _ fun j hj => hi_ne i hi j hj, kp3 _ (by omega), kH2 i hi]
  have eZ : s8.gpr .r19 = 0 := by rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr]; rfl
  have eW : (s8.gpr .r20).toNat = H 3 / 2 ^ 32 * 2 ^ 32 := by
    rw [u8.gpr, u7.gpr, toNat_shl, toNat_shr, show pw 10 = pw (7 + 3) from rfl, k6 _ (by decide),
      kH4 3 (by decide), ← hH]
    have := (s.gpr (pw (7 + 3))).isLt
    rw [Nat.mod_eq_of_lt (by omega_arith)]
  have hH8 : ∀ i < 7, (s8.gpr (pw (7 + i))).toNat = H i := fun i hi => by
    rw [k8 _ (by omega), kH4 i hi, ← hH]
  have hsrc3 : colsV (fun j => (s8.gpr (hiReg j)).toNat) 7 = colsV (hiW H) 7 := colsV_congr fun j hj => by
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [hiReg, hiW, Nat.reduceLT, ↓reduceIte, Nat.reduceEqDiff, eZ, eW] <;>
      first | rfl | exact hH8 _ (by decide)
  refine WP.append (chainN_ok (src := hiReg) hiReg_ne 7 (Nat.le_refl _)) fun s9 ⟨v9, r9, k9, m9⟩ => ?_
  simp only [show (7 : Nat) ≠ 0 from by decide, ↓reduceIte] at v9
  rw [hsrc3] at v9
  have e94 : (s9.gpr .r4).toNat = s1.ca.toNat + s4.ca.toNat := by
    rw [k9 _ fun j hj e => (pw_facts j (by omega)).1 e.symm, u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), e5]
  have e9Z : s9.gpr .r19 = 0 := by rw [k9 _ fun j hj e => (pw_ne j (by omega)).2.1 e.symm, eZ]
  refine wp_addze fun s10 u10 => wp_lsl (by decide) fun s11 u11 => ?_
  have c9 : s9.ca.toNat ≤ 1 := Bool.toNat_le _
  have e10 : (s10.gpr .r4).toNat = s1.ca.toNat + s4.ca.toNat + s9.ca.toNat := by
    have hv := u10.val; have := u10.ca; rw [e94] at hv; omega
  -- The folds.
  have fold_val : ∀ (t : State) (c : Nat), (t.gpr .r4).toNat = c → (t.gpr .r5).toNat = 2 ^ 32 * c →
      t.gpr .r19 = 0 → colsV (fun j => (t.gpr (foldReg j)).toNat) 7 = c + 2 ^ 224 * c := by
    intro t c h4 h5 h18
    simp only [colsV, foldReg, Nat.reduceEqDiff, ↓reduceIte, h4, h5, h18]
    have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [z]; omega
  have e11r5 : (s11.gpr .r5).toNat = 2 ^ 32 * (s1.ca.toNat + s4.ca.toNat + s9.ca.toNat) := by
    rw [u11.gpr, toNat_shl, e10, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have hf1 := fold_val s11 _ (by rw [u11.other _ (by decide), e10]) e11r5
    (by rw [u11.other _ (by decide), u10.other _ (by decide), e9Z])
  refine WP.append (chainN_ok (src := foldReg) foldReg_ne 7 (Nat.le_refl _)) fun s12 ⟨v12, r12, k12, m12⟩ => ?_
  simp only [show (7 : Nat) ≠ 0 from by decide, ↓reduceIte] at v12
  rw [hf1] at v12
  refine capture_ok fun s13 r13 m13 e13 => wp_lsl (by decide) fun s14 u14 => ?_
  have c12 : s12.ca.toNat ≤ 1 := Bool.toNat_le _
  have e14Z : s14.gpr .r19 = 0 := by
    rw [u14.other _ (by decide), r13.gpr _ (by decide), k12 _ fun j hj e => (pw_ne j (by omega)).2.1 e.symm,
      u11.other _ (by decide), u10.other _ (by decide), e9Z]
  have hf2 := fold_val s14 s12.ca.toNat (by rw [u14.other _ (by decide), e13])
    (by rw [u14.gpr, toNat_shl, e13, Nat.mod_eq_of_lt (by omega), Nat.mul_comm])
    e14Z
  refine WP.mono (chainN_ok (src := foldReg) foldReg_ne 7 (Nat.le_refl _)) fun s15 ⟨v15, r15, k15, m15⟩ => ?_
  simp only [show (7 : Nat) ≠ 0 from by decide, ↓reduceIte] at v15
  rw [hf2] at v15
  -- The registers and memory along the way.
  have hr : Rest clobR s s15 := r1.trans ((r2.mono (by decide)).trans (r3.trans (r4.trans
    ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
    ((u8.rest (by decide)).trans (r9.trans ((u10.rest (by decide)).trans ((u11.rest (by decide)).trans
    (r12.trans ((r13.mono (by decide)).trans ((u14.rest (by decide)).trans r15)))))))))))))
  refine ⟨hc.of_rest hr (by decide), hr, by
    rw [m15, u14.mem, m13, m12, u11.mem, u10.mem, m9, u8.mem, u7.mem, u6.mem, u5.mem, m4, m3, m2, m1], ?_⟩
  -- The value.
  have p1 : colsV (fun j => (s.gpr (pw (7 + j))).toNat) 7 = colsV H 7 := by rw [← hH]
  rw [p1, colsV_split H] at v1
  have p3 : colsV (fun j => (s3.gpr (pw j)).toNat) 7 = colsV (fun j => (s1.gpr (pw j)).toNat) 7 :=
    colsV_congr fun j hj => by rw [kp3 j (by omega), r2.gpr _ (by simp; exact (pw_facts j (by omega)).1)]
  have p3r : colsV (fun j => (s3.gpr (rotReg j)).toNat) 7 = colsV (rotW H) 7 :=
    colsV_congr fun j hj => by
      rw [v3 j hj, ← hH]
      simp only [rotW]
      rw [kH2 _ (Nat.mod_lt _ (by decide)), kH2 _ (Nat.mod_lt _ (by decide))]
  rw [p3, p3r, colsV_rotW] at v4
  have p8 : colsV (fun j => (s8.gpr (pw j)).toNat) 7 = colsV (fun j => (s4.gpr (pw j)).toNat) 7 :=
    colsV_congr fun j hj => by rw [k8 j (by omega)]
  rw [p8, colsV_hiW] at v9
  have p11 : colsV (fun j => (s11.gpr (pw j)).toNat) 7 = colsV (fun j => (s9.gpr (pw j)).toNat) 7 :=
    colsV_congr fun j hj => by
      rw [u11.other _ (pw_facts j (by omega)).2.1, u10.other _ (pw_facts j (by omega)).1]
  rw [p11] at v12
  have p14 : colsV (fun j => (s14.gpr (pw j)).toNat) 7 = colsV (fun j => (s12.gpr (pw j)).toNat) 7 :=
    colsV_congr fun j hj => by
      rw [u14.other _ (pw_facts j (by omega)).2.1, r13.gpr _ (by simp; exact (pw_facts j (by omega)).1)]
  rw [p14] at v15
  rw [show pwSum s 14 = colsV (fun j => (s.gpr (pw j)).toNat) 14 from rfl, colsV_14]
  rw [p1, colsV_split H]
  have hS := colsV_lt (fun j => (s9.gpr (pw j)).isLt) 7
  have hS9 := colsV_lt (fun j => (s12.gpr (pw j)).isLt) 7
  have e448 : (2 ^ 64) ^ 7 = (2 : Nat) ^ 224 * 2 ^ 224 := by
    rw [← Nat.pow_mul, show 64 * 7 = 32 * 14 from rfl]; exact pow448
  have c15 : s15.ca.toNat ≤ 1 := Bool.toNat_le _
  have c9' : s9.ca.toNat ≤ 1 := Bool.toNat_le _
  exact reduce_arith (L := colsV (fun j => (s.gpr (pw j)).toNat) 7) (Lo := loP H) (Hi := hiP H)
    (S := colsV (fun j => (s9.gpr (pw j)).toNat) 7) (c := (s10.gpr .r4).toNat)
    (S9 := colsV (fun j => (s12.gpr (pw j)).toNat) 7) (c9 := s12.ca.toNat)
    (S11 := colsV (fun j => (s15.gpr (pw j)).toNat) 7) (c11 := s15.ca.toNat)
    (by omega) (e448 ▸ hS) (e448 ▸ hS9) c15 (by rw [e10]; omega) (by rw [e10]; omega) (by omega)

/-! ## The multiplication in registers -/

theorem slotsOf_mem {R : Nat → Reg} {n : Nat} {p : Reg × Nat} (hp : p ∈ slotsOf R n) :
    ∃ i < n, p = (R i, 8 * i) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem slotsOf_fit {R : Nat → Reg} {n base : Nat} (h4 : base % 4 = 0) (hb : base + 8 * n ≤ 4096) :
    ∀ p ∈ slotsOf R n, p.2 % 4 = 0 ∧ base + p.2 + 8 ≤ 4096 := fun p hp => by
  obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp
  exact ⟨by omega, by omega⟩

theorem opsA_in : ∀ p ∈ slotsOf opA 7, p.1 ∈ clobR := by decide

theorem opsB_in : ∀ p ∈ slotsOf opB 7, p.1 ∈ clobR := by decide

/-- The doublewords at `B + 8 i` of `saveMem` of `slotsOf R n` hold the registers. -/
theorem saved_dw {R : Nat → Reg} {n : Nat} (hf : Fits (slotsOf R n)) (m : Mem) (B : Addr)
    (g : Reg → BitVec 64) {i : Nat} (hi : i < n) :
    (saveMem m B g (slotsOf R n)).readW (B + BitVec.ofNat 64 (8 * i)) 64 = g (R i) :=
  saveMem_saved hf m B g (R i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)


/-- `mulX o x y`: `[o] = [x] · [y]` modulo `p`, in registers it does not restore. -/
theorem mulX_ok {o x y : Nat} (ho : o + 56 ≤ ACC) (hx : x + 56 ≤ ACC)
    (hy : y + 56 ≤ ACC) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) (ho4 : o % 4 = 0) {s : State}
    (hc : Ctx b s) :
    WP isa (mulP o x y) s fun s' => Ctx b s' ∧ Rest clobR s s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := by
  have hA := ACC_eq
  unfold mulP mulX
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The operands.
  refine ldsAt_ok (l := slotsOf opA 7) hx4 (slotsOf_fit hx4 (by omega)) (by decide) (by decide) hc
    fun s2 hc2 r2 m2 v2 => ?_
  refine ldsAt_ok (l := slotsOf opB 7) hy4 (slotsOf_fit hy4 (by omega)) (by decide) (by decide) hc2
    fun s3 hc3 r3 m3 v3 => ?_
  have opsA : ∀ i < 7, (s3.gpr (opA i)).toNat = ew s.mem b x i := fun i hi => by
    rw [r3.gpr _ (by revert i; decide), v2 (opA i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩),
      Offset.add_add]; rfl
  have opsB : ∀ j < 7, (s3.gpr (opB j)).toNat = ew s.mem b y j := fun j hj => by
    rw [v3 (opB j, 8 * j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩), m2, Offset.add_add]; rfl
  -- The product.
  refine wp_li (by decide) fun s5 u5 => wp_li (by decide) fun s6 u6 => ?_
  have hr6 : Rest clobR s3 s6 := (u5.rest (by decide)).trans (u6.rest (by decide))
  refine WP.append (columns_ok (b := b) (hc3.of_rest hr6 (by decide))
    (by rw [u6.other _ (by decide), u5.gpr]; rfl) (by rw [u6.gpr]; rfl)) fun s7 ⟨hc7, r7, m7, v7⟩ => ?_
  have hA7 : colsV (fun i => (s6.gpr (opA i)).toNat) 7 = V s.mem b x := by
    rw [V_eq_cols]; exact colsV_congr fun i hi => by
      rw [u6.other _ (by revert i; decide), u5.other _ (by revert i; decide), opsA i hi]
  have hB7 : colsV (fun j => (s6.gpr (opB j)).toNat) 7 = V s.mem b y := by
    rw [V_eq_cols]; exact colsV_congr fun j hj => by
      rw [u6.other _ (by revert j; decide), u5.other _ (by revert j; decide), opsB j hj]
  rw [hA7, hB7] at v7
  refine WP.append (reduceR_ok hc7) fun s8 ⟨hc8, r8, m8, v8⟩ => ?_
  -- The result stored at `o`.
  refine stdsAt_ok (l := slotsOf pw 7) ho4 (slotsOf_fit ho4 (by omega)) hc8 fun s9 g9 rd9 wr9 sp9 mem9 => ?_
  refine WP.block_nil ⟨⟨by rw [g9]; exact hc8.r6, by rw [wr9]; exact hc8.wr⟩,
    ⟨fun r hr => ?_, by rw [rd9, r8.rd, r7.rd, u6.rd, u5.rd, r3.rd, r2.rd],
      by rw [wr9, r8.wr, r7.wr, u6.wr, u5.wr, r3.wr, r2.wr], by rw [sp9, r8.sp, r7.sp, u6.sp, u5.sp, r3.sp, r2.sp]⟩,
    ?_, ?_⟩
  · rw [congrFun g9, r8.gpr _ hr, r7.gpr _ hr, hr6.gpr _ hr,
      r3.gpr _ (fun h => hr (by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact opsB_in p hp)),
      r2.gpr _ (fun h => hr (by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact opsA_in p hp))]
  · rw [mem9, m8, m7, u6.mem, u5.mem, m3, m2]
    exact saveMem_frame_base (fun p hp => by obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp; omega) (by decide) _ _ _
  · rw [V_eq_cols, ← v7, ← v8]
    congr 1
    refine colsV_congr fun k hk => ?_
    rw [mem9]
    show (Mem.readW _ _ 64).toNat = _
    rw [← Offset.add_add, saved_dw (by decide) _ _ _ hk]

end

end VG.Proof.X448.PPC64LE
