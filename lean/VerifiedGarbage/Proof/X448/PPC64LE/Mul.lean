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

end

end VG.Proof.X448.PPC64LE
