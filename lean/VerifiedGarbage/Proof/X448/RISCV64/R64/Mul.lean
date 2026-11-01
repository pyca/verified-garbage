module

public import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Reduce
import VerifiedGarbage.Proof.X448.RISCV64.R64.Macc
public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide

/-!
# X448 on RISC-V, 64-bit limbs: a field multiplication

`mul o x y` stores at `o` a number congruent to `[x] · [y]` (`mul_ok`): the
fourteen words of the product or the square at `ACC`, then their reduction
(`Proof/X448/RISCV64/R64/Reduce.lean`).

* `product x y` (`product_ok`): `b₀–b₅` in registers (`BRegs`), with `b₆` in
  `b₀`'s register from column 6 on, each term `a_i b_j` with `a_i` loaded
  (`mulTerm_ok`), the columns by induction (`columns_ok`); the columns sum to
  the product (`mulCols_sum`).
* `square x` (`square_ok`): the cross products `a_j a_i` (`j < i`), with
  `a₀–a₅` in registers (`ARegs`) and `a₆` loaded (`sqTerm_ok`); then
  `dblStep x k` turns word `k` of their sum `X` into word `k` of
  `2 X + Σ a_i² 2¹²⁸ⁱ` (`dblStep_ok`): `X`'s word doubled, with the top bit
  of the word below shifted in (`dbw`), plus word `k` of the squares (`dq`),
  plus the carry; twice the cross products plus the squares are the square
  (`sqCols_sum`).
-/

-- separate module: its proofs (about 6 s) cost more than its imports, and its importer's
-- changes need not re-check them

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.X448.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (ACC)

/-- The registers of `b`: `bReg j` holds `b_j`, for `j ≠ 6` before column 6's
reload (`ph = false`) and `j ≠ 0` after it. -/
def BRegs (Y : Nat → Nat) (ph : Bool) (s : State) : Prop :=
  ∀ j < 7, (if ph then j ≠ 0 else j ≠ 6) → (s.gpr (bReg j)).toNat = Y j

/-- The registers of `b` are not the accumulator's or the temporaries. -/
theorem bReg_ne' : ∀ j < 7, bReg j ≠ .a4 ∧ bReg j ≠ .a5 ∧ bReg j ≠ .a6 ∧
    bReg j ≠ .a7 ∧ bReg j ≠ .t0 ∧ bReg j ∈ clob64 := by decide

theorem bReg_ne (k : Nat) {j : Nat} (hj : j < 7) : bReg j ≠ rr k ∧ bReg j ≠ rr (k + 1) ∧
    bReg j ≠ rr (k + 2) ∧ bReg j ≠ .a7 ∧ bReg j ≠ .t0 ∧ bReg j ∈ clob64 := by
  obtain ⟨h4, h5, h6, h7, h0, hc⟩ := bReg_ne' j hj
  refine ⟨?_, ?_, ?_, h7, h0, hc⟩ <;>
  · rcases rr_cases (k := _) with e | e | e <;> rw [e] <;> with_reducible assumption

theorem BRegs.of_gpr {Y : Nat → Nat} {ph : Bool} {s s' : State} (h : BRegs Y ph s)
    (hg : ∀ j < 7, s'.gpr (bReg j) = s.gpr (bReg j)) : BRegs Y ph s' :=
  fun j hj hp => by rw [hg j hj]; exact h j hj hp

/-- The columns of a product: column `k` is the sum of `a_i b_j` with `i + j = k`. -/
def mulF (X Y : Nat → Nat) (p : Nat × Nat) : Nat := X p.1 * Y p.2

def mulCs (X Y : Nat → Nat) (k : Nat) : Nat := tsum (mulF X Y) (colPairs k)

section
variable {b : Addr}

/-- The element at `x`, unchanged in a frame of `ACC`. -/
theorem dw_acc {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] m m') {d : Nat}
    (hd : d + 8 ≤ ACC) : dw m' b d = dw m b d :=
  dw_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := ACC_eq
    exact Offset.disjoint _ (.inl hd) (by omega) (by omega)

theorem term_regs {s s1 s2 : State} {k : Nat} {v : BitVec 64} (u1 : Upd s s1 .t0 v)
    (k2 : Keeps [rr k, rr (k + 1), rr (k + 2), .a7, .t0] s1 s2) {r : Reg} (hr : r ≠ rr k)
    (hr1 : r ≠ rr (k + 1)) (hr2 : r ≠ rr (k + 2)) (hr7 : r ≠ .a7) (hr0 : r ≠ .t0) :
    s2.gpr r = s.gpr r := by
  rw [k2.1 r (by simp [hr, hr1, hr2, hr7, hr0]), u1.other _ hr0]

/-- A term `a_i b_j` of column `k`, other than `a₆ b₀`. -/
theorem mulTerm_ok {s0 : State} {x y : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) {k i j : Nat}
    (hk : k < 14) (hi : i < 7) (hj : j < 7) {ph : Bool} (hp : if ph then j ≠ 0 else j ≠ 6)
    (hne : ¬(i = 6 ∧ j = 0)) :
    TermOk b s0 k (BRegs (fun j => dw s0.mem b (y + 8 * j)) ph)
      (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)))
      (mulTerm x y k) (i, j) := by
  intro s hB hc hr hf
  obtain ⟨h01, h02, h12, h07, h00, h17, h10, h27, h20, -⟩ := rr_ne k hk
  obtain ⟨hb0, hb1, hb2, hb7, hbt, hbc⟩ := bReg_ne k hj
  have hA := ACC_eq
  simp only [mulTerm, hne, ite_false, List.append_nil]
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => ?_
  refine WP.mono (macc_ok h01 h02 h12 h07 h00 h17 h10 h27 h20 (by decide) hb7) fun s2 ⟨e2, k2⟩ => ?_
  have hr2 : Rest clob64 s s2 :=
    (u1.rest (ws := clob64) (by decide)).trans ((Keeps.rest k2).mono fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl
      exacts [rr_clob _, rr_clob _, rr_clob _, by decide, by decide])
  have hm2 : s2.mem = s.mem := by rw [k2.2.1, u1.mem]
  have hv1 : val3 s1 (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) := by
    simp only [val3, u1.other _ h00, u1.other _ h10, u1.other _ h20]
  have ex : (s1.gpr .t0).toNat = dw s0.mem b (x + 8 * i) := by
    rw [u1.gpr]; exact dw_acc hf (by omega)
  have ey : (s1.gpr (bReg j)).toNat = dw s0.mem b (y + 8 * j) := by
    rw [u1.other _ hbt]; exact hB j hj hp
  refine ⟨hB.of_gpr fun j' hj' => ?_, hc.of_rest hr2 (by decide), hr.trans hr2, by rw [hm2]; exact hf,
    by rw [hm2], fun hb => ?_⟩
  · obtain ⟨c0, c1, c2, c7, ct, -⟩ := bReg_ne k hj'
    exact term_regs u1 k2 c0 c1 c2 c7 ct
  · rw [e2 (by rw [hv1, ex, ey]; exact hb), hv1, ex, ey]; rfl

theorem bReg_ne_w0 : ∀ j < 7, j ≠ 0 → j ≠ 6 → bReg j ≠ w 0 := by decide

/-- The term `a₆ b₀` of column 6, then `b₆` loaded into `b₀`'s register. -/
theorem mulTerm60_ok {s0 : State} {x y : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0)
    (hy : y + 56 ≤ ACC) (hy8 : y % 8 = 0) {s : State}
    (hB : BRegs (fun j => dw s0.mem b (y + 8 * j)) false s) (hc : Ctx b s) (hr : Rest clob64 s0 s)
    (hf : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem) :
    WP isa (.block (mulTerm x y 6 (6, 0))) s fun s' =>
      BRegs (fun j => dw s0.mem b (y + 8 * j)) true s' ∧ Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s'.mem ∧ accW s'.mem b 6 = accW s.mem b 6 ∧
      (val3 s (rr 6) (rr 7) (rr 8) + mulF (fun i => dw s0.mem b (x + 8 * i))
          (fun j => dw s0.mem b (y + 8 * j)) (6, 0) < 2 ^ 192 →
        val3 s' (rr 6) (rr 7) (rr 8) = val3 s (rr 6) (rr 7) (rr 8) +
          mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) (6, 0)) := by
  have hA := ACC_eq
  have e : mulTerm x y 6 (6, 0) =
      (.load .d .t0 .a3 (x + 8 * 6) :: macc (rr 6) (rr 7) (rr 8) .t0 (bReg 0)) ++
        [.load .d (w 0) .a3 (y + 48)] := rfl
  rw [e, List.cons_append]
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => ?_
  refine WP.append (macc_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  have hc2 : Ctx b s2 := hc.of_rest ((u1.rest (ws := clob64) (by decide)).trans
    ((Keeps.rest k2).mono (by decide))) (by decide)
  refine ld_ok hc2 (by omega) (by omega) fun s3 u3 => WP.block_nil ?_
  have hr3 : Rest clob64 s s3 := (u1.rest (by decide)).trans (((Keeps.rest k2).mono (by decide)).trans
    (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, k2.2.1, u1.mem]
  have hv1 : val3 s1 (rr 6) (rr 7) (rr 8) = val3 s (rr 6) (rr 7) (rr 8) := by
    simp only [val3, u1.other _ (show rr 6 ≠ .t0 by decide), u1.other _ (show rr 7 ≠ .t0 by decide),
      u1.other _ (show rr 8 ≠ .t0 by decide)]
  have hv3 : val3 s3 (rr 6) (rr 7) (rr 8) = val3 s2 (rr 6) (rr 7) (rr 8) := by
    simp only [val3, u3.other _ (show rr 6 ≠ w 0 by decide), u3.other _ (show rr 7 ≠ w 0 by decide),
      u3.other _ (show rr 8 ≠ w 0 by decide)]
  have ex : (s1.gpr .t0).toNat = dw s0.mem b (x + 8 * 6) := by
    rw [u1.gpr]; exact dw_acc hf (by omega)
  have ey : (s1.gpr (bReg 0)).toNat = dw s0.mem b (y + 8 * 0) := by
    rw [u1.other _ (by decide)]; exact hB 0 (by decide) (by decide)
  refine ⟨fun j hj hp => ?_, hc.of_rest hr3 (by decide), hr.trans hr3, by rw [hm3]; exact hf,
    by rw [hm3], fun hb => ?_⟩
  · simp only [ite_true] at hp
    by_cases h6 : j = 6
    · subst h6
      rw [show bReg 6 = w 0 by rfl, u3.gpr, k2.2.1, u1.mem]
      exact (dw_acc hf (by omega)).trans (by rfl)
    · obtain ⟨c0, c1, c2, c7, ct, -⟩ := bReg_ne 6 hj
      have hw : bReg j ≠ w 0 := bReg_ne_w0 j hj hp h6
      rw [u3.other _ hw, term_regs u1 k2 c0 c1 c2 c7 ct]
      exact hB j hj (by simp only [Bool.false_eq_true, ite_false]; exact h6)
  · rw [hv3, e2 (by rw [hv1, ex, ey]; exact hb), hv1, ex, ey]; rfl

/-- The terms of a column other than 6 are valid in its phase. -/
theorem colPairs_ok : ∀ k < 14, k ≠ 6 → ∀ p ∈ colPairs k, p.1 < 7 ∧ p.2 < 7 ∧
    (if decide (7 ≤ k) then p.2 ≠ 0 else p.2 ≠ 6) ∧ ¬(p.1 = 6 ∧ p.2 = 0) := by decide

theorem colPairs_len : ∀ k < 14, (colPairs k).length ≤ 7 := by decide

theorem colPairs_six : colPairs 6 = (6, 0) :: [(5, 1), (4, 2), (3, 3), (2, 4), (1, 5), (0, 6)] := by decide

theorem mulF_le (X Y : Nat → Nat) (hX : ∀ i, X i < 2 ^ 64) (hY : ∀ j, Y j < 2 ^ 64) (p : Nat × Nat) :
    mulF X Y p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := hX p.1; omega) (by have := hY p.2; omega)

theorem tsum_mul_lt {X Y : Nat → Nat} (hX : ∀ i, X i < 2 ^ 64) (hY : ∀ j, Y j < 2 ^ 64)
    {ps : List (Nat × Nat)} (hl : ps.length ≤ 7) : tsum (mulF X Y) ps < 7 * 2 ^ 128 := by
  have := tsum_le (ps := ps) fun p _ => mulF_le X Y hX hY p
  have : ps.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) ≤ 7 * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) :=
    Nat.mul_le_mul_right _ hl
  omega

/-- Column `k` of `product x y`. -/
theorem mulCol_ok {s0 : State} {x y : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0)
    (hy : y + 56 ≤ ACC) (hy8 : y % 8 = 0) {k : Nat} (hk : k < 14) {s : State}
    (h : ColInv b s0 (mulCs (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j))) k s)
    (hB : BRegs (fun j => dw s0.mem b (y + 8 * j)) (decide (7 ≤ k)) s) :
    WP isa (.block (mulCol x y k)) s fun s' =>
      ColInv b s0 (mulCs (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j))) (k + 1) s' ∧
      BRegs (fun j => dw s0.mem b (y + 8 * j)) (decide (7 ≤ k + 1)) s' := by
  have hX : ∀ i, dw s0.mem b (x + 8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
  have hY : ∀ j, dw s0.mem b (y + 8 * j) < 2 ^ 64 := fun j => dw_lt _ _ _
  have hinv : ∀ ph s s', BRegs (fun j => dw s0.mem b (y + 8 * j)) ph s →
      (∀ r, r ≠ rr k → s'.gpr r = s.gpr r) → BRegs (fun j => dw s0.mem b (y + 8 * j)) ph s' :=
    fun _ _ _ hB' hg => hB'.of_gpr fun j hj => hg _ (bReg_ne k hj).1
  by_cases h6 : k = 6
  · subst h6
    have e : mulCol x y 6 = mulTerm x y 6 (6, 0) ++
        ([(5, 1), (4, 2), (3, 3), (2, 4), (1, 5), (0, 6)].flatMap (mulTerm x y 6) ++ colEnd 6) := by
      rw [mulCol, colPairs_six, List.flatMap_cons, List.append_assoc]
    rw [e]
    have hv0 : val3 s (rr 6) (rr 7) (rr 8) = (s.gpr (rr 6)).toNat + 2 ^ 64 * (s.gpr (rr 7)).toNat := by
      simp only [val3, h.top]; rfl
    have hl := (s.gpr (rr 6)).isLt
    have hh := (s.gpr (rr 7)).isLt
    have hbd := tsum_mul_lt hX hY (colPairs_len 6 (by decide))
    rw [colPairs_six, tsum_cons] at hbd
    refine WP.append (mulTerm60_ok hx hx8 hy hy8 hB h.ctx h.rest h.frame)
      fun s1 ⟨hB1, hc1, hr1, hf1, ha1, hv1⟩ => ?_
    have hv1 := hv1 (by rw [hv0]; omega_arith)
    refine WP.append (terms_ok (k := 6) (Inv := BRegs (fun j => dw s0.mem b (y + 8 * j)) true)
      (f := mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)))
      (code := mulTerm x y 6) _ (fun p hp => ?_) s1 hB1 hc1 hr1 hf1 (by rw [hv1, hv0]; omega_arith))
      fun s2 ⟨hB2, hc2, hr2, hf2, ha2, hv2⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact mulTerm_ok hx hx8 (by decide) (by decide) (by decide) (by decide) (by decide)
    refine WP.mono (colEnd_ok (cs := mulCs _ _) (by decide) hc2 hr2 hf2 ?_) fun s3 ⟨h3, hg3⟩ =>
      ⟨h3, hinv true s2 s3 hB2 hg3⟩
    have hval := h.val
    simp only [Nat.reduceAdd] at hval hv2 ⊢
    rw [ha2, ha1, hv2, hv1, hv0, colsV, ← hval, mulCs, colPairs_six, tsum_cons _ (6, 0)]
    omega_arith
  · have hok := colPairs_ok k hk h6
    have hph : decide (7 ≤ k + 1) = decide (7 ≤ k) := by
      rcases Nat.lt_or_ge k 6 with h' | h' <;> simp only [decide_eq_decide] <;> omega
    rw [hph]
    exact column_ok hk (colPairs k) (fun p hp => by
        obtain ⟨h1, h2, h3, h4⟩ := hok p hp
        exact mulTerm_ok hx hx8 hk h1 h2 h3 h4) rfl
      (tsum_mul_lt hX hY (colPairs_len k hk)) (hinv _) h hB

theorem colPairs_eval : ∀ k < 14, colPairs k = ((List.range 7).reverse.filter fun i => i ≤ k ∧ k - i < 7).map
    fun i => (i, k - i) := fun _ _ => rfl

/-- The columns sum to the product. -/
theorem mulCols_sum (X Y : Nat → Nat) : colsV (mulCs X Y) 14 = val7 X * val7 Y := by
  simp only [colsV, val7]
  generalize 2 ^ 64 = B
  simp only [mulCs, colPairs, tsum, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mulF, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
  grind

/-- `product x y`: the fourteen words of `[x] · [y]` at `ACC`. -/
theorem product_ok {x y : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) (hy : y + 56 ≤ ACC)
    (hy8 : y % 8 = 0) {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (product x y)) s0 fun s' => Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s'.mem ∧
      accW s'.mem b 14 = Proof.X448.RISCV64.V s0.mem b x * Proof.X448.RISCV64.V s0.mem b y := by
  have hA := ACC_eq
  unfold product
  rw [List.append_assoc]
  refine WP.append (ld6_ok (by omega) hy8 hc) fun s1 ⟨h1, hr1, hm1⟩ => ?_
  refine WP.append zero3_ok fun s2 ⟨e4, e5, e6, hr2, hm2⟩ => ?_
  have hr12 := hr1.trans (hr2.mono (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr12 (by decide)
  have hinit : ColInv b s0 (mulCs (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j))) 0 s2 :=
    ⟨hc2, hr12, by rw [hm2, hm1]; exact Frame.refl _ _, e6, by
      simp only [accW, colsV, show rr 0 = .a4 from rfl, show rr (0 + 1) = .a5 from rfl, e4, e5]; rfl⟩
  have hB : BRegs (fun j => dw s0.mem b (y + 8 * j)) (decide (7 ≤ 0)) s2 := fun j hj hp => by
    simp only [Nat.not_le.mpr (show 0 < 7 by decide), decide_false, Bool.false_eq_true, ite_false] at hp
    have hj6 : j < 6 := by omega
    rw [show bReg j = w j from by unfold bReg; rw [Nat.mod_eq_of_lt hj6],
      hr2.gpr _ (by revert hj6; revert j; decide), h1 j hj6]
  refine WP.mono (columns_ok (Inv := fun k => BRegs (fun j => dw s0.mem b (y + 8 * j)) (decide (7 ≤ k)))
    (fun k hk s h hi => mulCol_ok hx hx8 hy hy8 hk h hi) 14 (Nat.le_refl _) s2 hinit hB)
    fun s3 ⟨h3, _⟩ => ⟨h3.ctx, h3.rest, h3.frame, ?_⟩
  have hlt : val7 (fun i => dw s0.mem b (x + 8 * i)) * val7 (fun j => dw s0.mem b (y + 8 * j)) <
      (2 ^ 64) ^ 14 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (val7_lt fun i _ => dw_lt _ _ _)
      (val7_lt fun i _ => dw_lt _ _ _))
      (by rw [← Nat.pow_add])
  rw [h3.final (by rw [mulCols_sum]; exact hlt), mulCols_sum, V_eq, V_eq]

end

end

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.X448.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (ACC)

/-- `a₀–a₅` in `w 0`–`w 5`. -/
def ARegs (X : Nat → Nat) (s : State) : Prop := ∀ i < 6, (s.gpr (w i)).toNat = X i

/-- A cross term's value: `a_j a_i` for the term `(i, j)`. -/
def sqF (X : Nat → Nat) (p : Nat × Nat) : Nat := X p.2 * X p.1

/-- The cross terms of column `k`. -/
def sqPairs (k : Nat) : List (Nat × Nat) := (colPairs k).filter fun p => p.2 < p.1

def sqCs (X : Nat → Nat) (k : Nat) : Nat := tsum (sqF X) (sqPairs k)

theorem w_ne' : ∀ i < 6, w i ≠ .a4 ∧ w i ≠ .a5 ∧ w i ≠ .a6 ∧ w i ≠ .a7 ∧ w i ≠ .t0 := by decide

theorem w_ne_rr (k : Nat) {i : Nat} (hi : i < 6) : w i ≠ rr k ∧ w i ≠ rr (k + 1) ∧
    w i ≠ rr (k + 2) ∧ w i ≠ .a7 ∧ w i ≠ .t0 := by
  obtain ⟨h4, h5, h6, h7, h0⟩ := w_ne' i hi
  refine ⟨?_, ?_, ?_, h7, h0⟩ <;>
  · rcases rr_cases (k := _) with e | e | e <;> rw [e] <;> with_reducible assumption

theorem sqPairs_ok : ∀ k < 14, ∀ p ∈ sqPairs k, p.2 < 6 ∧ p.1 < 7 ∧ p.2 < p.1 := by decide

theorem sqPairs_len : ∀ k < 14, (sqPairs k).length ≤ 7 := by decide

section
variable {b : Addr}

/-- A cross term `a_j a_i` of column `k`. -/
theorem sqTerm_ok {s0 : State} {x : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) {k i j : Nat}
    (hk : k < 14) (hi : i < 7) (hj : j < 6) :
    TermOk b s0 k (ARegs fun i => dw s0.mem b (x + 8 * i)) (sqF fun i => dw s0.mem b (x + 8 * i))
      (sqTerm x k) (i, j) := by
  intro s hA hc hr hf
  obtain ⟨h01, h02, h12, h07, h00, h17, h10, h27, h20, -⟩ := rr_ne k hk
  obtain ⟨c0, c1, c2, c7, ct⟩ := w_ne_rr k hj
  have hAc := ACC_eq
  have hregs : ∀ {s1 s2 : State}, Keeps [rr k, rr (k + 1), rr (k + 2), .a7, .t0] s1 s2 →
      Rest clob64 s1 s2 := fun k2 => (Keeps.rest k2).mono fun r hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    exacts [rr_clob _, rr_clob _, rr_clob _, by decide, by decide]
  have hkeepA : ∀ {s1 s2 : State}, Keeps [rr k, rr (k + 1), rr (k + 2), .a7, .t0] s1 s2 →
      ARegs (fun i => dw s0.mem b (x + 8 * i)) s1 → ARegs (fun i => dw s0.mem b (x + 8 * i)) s2 :=
    fun k2 h1 i' hi' => by
      obtain ⟨d0, d1, d2, d7, dt⟩ := w_ne_rr k hi'
      rw [k2.1 _ (by simp [d0, d1, d2, d7, dt])]; exact h1 i' hi'
  by_cases h6 : i = 6
  · subst h6
    simp only [sqTerm, ite_true]
    refine ld_ok hc (by omega) (by omega) fun s1 u1 => ?_
    refine WP.mono (macc_ok h01 h02 h12 h07 h00 h17 h10 h27 h20 c7 (by decide)) fun s2 ⟨e2, k2⟩ => ?_
    have hr2 : Rest clob64 s s2 := (u1.rest (ws := clob64) (by decide)).trans (hregs k2)
    have hm2 : s2.mem = s.mem := by rw [k2.2.1, u1.mem]
    have hv1 : val3 s1 (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) := by
      simp only [val3, u1.other _ h00, u1.other _ h10, u1.other _ h20]
    have ey : (s1.gpr .t0).toNat = dw s0.mem b (x + 8 * 6) := by
      rw [u1.gpr]; exact (dw_acc hf (by omega)).trans (by rfl)
    have ex : (s1.gpr (w j)).toNat = dw s0.mem b (x + 8 * j) := by
      rw [u1.other _ ct]; exact hA j hj
    have hA1 : ARegs (fun i => dw s0.mem b (x + 8 * i)) s1 := fun i' hi' => by
      rw [u1.other _ (w_ne_rr k hi').2.2.2.2]; exact hA i' hi'
    refine ⟨hkeepA k2 hA1, hc.of_rest hr2 (by decide), hr.trans hr2, by rw [hm2]; exact hf,
      by rw [hm2], fun hb => ?_⟩
    rw [e2 (by rw [hv1, ex, ey]; exact hb), hv1, ex, ey]; rfl
  · simp only [sqTerm, h6, ite_false]
    obtain ⟨d0, d1, d2, d7, dt⟩ := w_ne_rr k (show i < 6 by omega)
    refine WP.mono (macc_ok h01 h02 h12 h07 h00 h17 h10 h27 h20 c7 d7) fun s2 ⟨e2, k2⟩ =>
      ⟨hkeepA k2 hA, hc.of_rest (hregs k2) (by decide), hr.trans (hregs k2),
        by rw [k2.2.1]; exact hf, by rw [k2.2.1], fun hb => ?_⟩
    have ex := hA j hj
    have ey := hA i (by omega)
    rw [e2 (by rw [ex, ey]; exact hb), ex, ey]; rfl

/-- Column `k` of the cross products. -/
theorem sqCol_ok {s0 : State} {x : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) {k : Nat}
    (hk : k < 14) {s : State} (h : ColInv b s0 (sqCs fun i => dw s0.mem b (x + 8 * i)) k s)
    (hA : ARegs (fun i => dw s0.mem b (x + 8 * i)) s) :
    WP isa (.block (sqCol x k)) s fun s' =>
      ColInv b s0 (sqCs fun i => dw s0.mem b (x + 8 * i)) (k + 1) s' ∧
      ARegs (fun i => dw s0.mem b (x + 8 * i)) s' := by
  have hX : ∀ i, dw s0.mem b (x + 8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
  have hle : ∀ p, sqF (fun i => dw s0.mem b (x + 8 * i)) p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    fun p => by
      dsimp only [sqF]
      have := hX p.2; have := hX p.1
      exact Nat.mul_le_mul (by omega) (by omega)
  have hbd : tsum (sqF fun i => dw s0.mem b (x + 8 * i)) (sqPairs k) < 7 * 2 ^ 128 := by
    have := tsum_le (ps := sqPairs k) fun p _ => hle p
    have : (sqPairs k).length * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) ≤ 7 * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) :=
      Nat.mul_le_mul_right _ (sqPairs_len k hk)
    omega
  exact column_ok hk (sqPairs k) (fun p hp => by
      obtain ⟨h1, h2, -⟩ := sqPairs_ok k hk p hp
      exact sqTerm_ok hx hx8 hk h2 h1) rfl hbd
    (fun _ _ hA' hg i hi => by rw [hg _ (w_ne_rr k hi).1]; exact hA' i hi) h hA

end

/-- The squares `a_i²` at `2¹²⁸ⁱ`. -/
def dsq (X : Nat → Nat) : Nat :=
  X 0 * X 0 + (2 ^ 64) ^ 2 * (X 1 * X 1) + (2 ^ 64) ^ 4 * (X 2 * X 2) + (2 ^ 64) ^ 6 * (X 3 * X 3) +
    (2 ^ 64) ^ 8 * (X 4 * X 4) + (2 ^ 64) ^ 10 * (X 5 * X 5) + (2 ^ 64) ^ 12 * (X 6 * X 6)

/-- Twice the cross products' columns, plus the squares, are the square. -/
theorem sqCols_sum (X : Nat → Nat) : 2 * colsV (sqCs X) 14 + dsq X = val7 X * val7 X := by
  simp only [colsV, val7, dsq]
  generalize 2 ^ 64 = B
  simp only [sqCs, sqPairs, colPairs, tsum, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil,
    List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sqF, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
  grind

end

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.X448.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (ACC)

/-- The top bit of the word below `k`. -/
def cp (C : Nat → Nat) (k : Nat) : Nat := if k = 0 then 0 else C (k - 1) / 2 ^ 63

/-- Word `k` of `2 X`, for `X`'s words `C`. -/
def dbw (C : Nat → Nat) (k : Nat) : Nat := C k * 2 % 2 ^ 64 + cp C k

/-- Word `k` of the squares `Σ a_i² 2¹²⁸ⁱ`. -/
def dq (X : Nat → Nat) (k : Nat) : Nat :=
  if k % 2 = 0 then X (k / 2) * X (k / 2) % 2 ^ 64 else X (k / 2) * X (k / 2) / 2 ^ 64

theorem colsV_add (f g : Nat → Nat) : ∀ n, colsV (fun c => f c + g c) n = colsV f n + colsV g n
  | 0 => rfl
  | n + 1 => by rw [colsV, colsV, colsV, colsV_add f g n, Nat.mul_add]; omega

/-- The doubled words are twice `X`, but for the top bit of the last. -/
theorem colsV_dbw {C : Nat → Nat} (hC : ∀ i, C i < 2 ^ 64) :
    ∀ n, colsV (dbw C) (n + 1) + (2 ^ 64) ^ (n + 1) * (C n / 2 ^ 63) = 2 * colsV C (n + 1)
  | 0 => by
    simp only [colsV, dbw, cp, ite_true, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one]
    have := hC 0
    omega
  | n + 1 => by
    have ih := colsV_dbw hC n
    rw [colsV, show colsV C (n + 1 + 1) = colsV C (n + 1) + (2 ^ 64) ^ (n + 1) * C (n + 1) from rfl,
      Nat.pow_succ (n := 2 ^ 64) (m := n + 1)]
    simp only [dbw, cp, show n + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
    have := hC (n + 1)
    have e : C (n + 1) * 2 % 2 ^ 64 + 2 ^ 64 * (C (n + 1) / 2 ^ 63) = 2 * C (n + 1) := by omega
    generalize (2 ^ 64) ^ (n + 1) = K at *
    generalize colsV (dbw C) (n + 1) = A at *
    generalize colsV C (n + 1) = B at *
    generalize C n / 2 ^ 63 = t at *
    generalize C (n + 1) * 2 % 2 ^ 64 = u at *
    generalize C (n + 1) / 2 ^ 63 = v at *
    generalize C (n + 1) = c at *
    generalize 2 ^ 64 = W at *
    grind

/-- The words of the squares are the squares. -/
theorem colsV_dq (X : Nat → Nat) : colsV (dq X) 14 = dsq X := by
  simp only [colsV, dq, dsq]
  simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]
  have h0 := Nat.mod_add_div (X 0 * X 0) (2 ^ 64)
  have h1 := Nat.mod_add_div (X 1 * X 1) (2 ^ 64)
  have h2 := Nat.mod_add_div (X 2 * X 2) (2 ^ 64)
  have h3 := Nat.mod_add_div (X 3 * X 3) (2 ^ 64)
  have h4 := Nat.mod_add_div (X 4 * X 4) (2 ^ 64)
  have h5 := Nat.mod_add_div (X 5 * X 5) (2 ^ 64)
  have h6 := Nat.mod_add_div (X 6 * X 6) (2 ^ 64)
  generalize X 0 * X 0 % 2 ^ 64 = l0 at *
  generalize X 1 * X 1 % 2 ^ 64 = l1 at *
  generalize X 2 * X 2 % 2 ^ 64 = l2 at *
  generalize X 3 * X 3 % 2 ^ 64 = l3 at *
  generalize X 4 * X 4 % 2 ^ 64 = l4 at *
  generalize X 5 * X 5 % 2 ^ 64 = l5 at *
  generalize X 6 * X 6 % 2 ^ 64 = l6 at *
  generalize X 0 * X 0 / 2 ^ 64 = u0 at *
  generalize X 1 * X 1 / 2 ^ 64 = u1 at *
  generalize X 2 * X 2 / 2 ^ 64 = u2 at *
  generalize X 3 * X 3 / 2 ^ 64 = u3 at *
  generalize X 4 * X 4 / 2 ^ 64 = u4 at *
  generalize X 5 * X 5 / 2 ^ 64 = u5 at *
  generalize X 6 * X 6 / 2 ^ 64 = u6 at *
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  generalize 2 ^ 64 = B
  grind

/-! ## The blocks of a step -/

variable {s : State}

set_option linter.unusedSimpArgs false in
theorem dbl1_ok :
    WP isa (.block [.shift .srl .d .a7 .a5 63]) s fun s' =>
      (s'.gpr .a7).toNat = (s.gpr .a5).toNat / 2 ^ 63 ∧ Keeps [.a7] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 63 < 64 by decide),
    RegUpd.gpr_write, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨toNat_shr _ _, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

set_option linter.unusedSimpArgs false in
theorem dbl2_ok :
    WP isa (.block [.shift .sll .d .a6 .a5 1, .logic .or .a6 .a6 .a7]) s fun s' =>
      ((s.gpr .a7).toNat ≤ 1 →
        (s'.gpr .a6).toNat = (s.gpr .a5).toNat * 2 % 2 ^ 64 + (s.gpr .a7).toNat) ∧
      Keeps [.a6] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 1 < 64 by decide),
    exec_logic, RegUpd.gpr_write, ite_true, Option.some.injEq, exists_eq_left', reduceCtorEq,
    ite_false]
  refine ⟨fun h => dbl_or _ _ h, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

set_option linter.unusedSimpArgs false in
theorem dbl3e_ok :
    WP isa (.block [.mul .t0 .t3 .t3, .mulhu .t3 .t3 .t3, .add .a6 .a6 .t0, .sltu .a7 .a6 .t0]) s
      fun s' => (s'.gpr .a6).toNat + 2 ^ 64 * (s'.gpr .a7).toNat =
          (s.gpr .a6).toNat + (s.gpr .t3).toNat * (s.gpr .t3).toNat % 2 ^ 64 ∧
        (s'.gpr .t3).toNat = (s.gpr .t3).toNat * (s.gpr .t3).toNat / 2 ^ 64 ∧
        Keeps [.t0, .t3, .a6, .a7] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mul, exec_mulhu, exec_add, exec_sltu,
    RegUpd.gpr_write, ite_true, Option.some.injEq, exists_eq_left', reduceCtorEq, ite_false]
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [Wide.carry, BitVec.toNat_mul]
  · rw [toNat_imm (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (mulhi_lt _ _)) (by decide))]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

set_option linter.unusedSimpArgs false in
theorem dbl3o_ok :
    WP isa (.block [.add .a6 .a6 .t3, .sltu .a7 .a6 .t3]) s
      fun s' => (s'.gpr .a6).toNat + 2 ^ 64 * (s'.gpr .a7).toNat =
          (s.gpr .a6).toNat + (s.gpr .t3).toNat ∧ Keeps [.a6, .a7] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, ite_true, Option.some.injEq, exists_eq_left', reduceCtorEq, ite_false]
  refine ⟨Wide.carry _ _, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

set_option linter.unusedSimpArgs false in
theorem dbl4_ok :
    WP isa (.block [.add .a6 .a6 .a4, .sltu .t0 .a6 .a4, .add .a4 .a7 .t0]) s
      fun s' => ((s.gpr .a7).toNat ≤ 1 → (s'.gpr .a6).toNat + 2 ^ 64 * (s'.gpr .a4).toNat =
          (s.gpr .a6).toNat + (s.gpr .a4).toNat + 2 ^ 64 * (s.gpr .a7).toNat) ∧
        Keeps [.a6, .t0, .a4] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, ite_true, Option.some.injEq, exists_eq_left', reduceCtorEq, ite_false]
  refine ⟨fun h7 => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have c := Wide.carry (s.gpr .a6) (s.gpr .a4)
    have l := Wide.carry_le (s.gpr .a6 + s.gpr .a4 < s.gpr .a4)
    generalize (if s.gpr .a6 + s.gpr .a4 < s.gpr .a4 then (1 : BitVec 64) else 0) = k at *
    rw [BitVec.toNat_add (s.gpr .a7), Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-! ## A step, and the square -/

section
variable {b : Addr}

/-- Before step `k` of the doubling, from `s0` (the start of `square x`):
the words of `X` from `k` on unchanged (`C`), `X`'s word `k - 1` in `a5`, the
high word of the last square in `t3` (for odd `k`), the carry in `a4`, and
the words below `k` with the carry the first `k` words of the square. -/
structure DblInv (b : Addr) (s0 : State) (x : Nat) (C : Nat → Nat) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem
  hi : ∀ i, k ≤ i → i < 14 → dw s.mem b (ACC + 8 * i) = C i
  prev : (s.gpr .a5).toNat = if k = 0 then 0 else C (k - 1)
  sqhi : k % 2 = 1 → (s.gpr .t3).toNat =
    dw s0.mem b (x + 8 * (k / 2)) * dw s0.mem b (x + 8 * (k / 2)) / 2 ^ 64
  cy : (s.gpr .a4).toNat ≤ 2
  val : accW s.mem b k + (2 ^ 64) ^ k * (s.gpr .a4).toNat =
    colsV (fun c => dbw C c + dq (fun i => dw s0.mem b (x + 8 * i)) c) k

theorem dbw_lt {C : Nat → Nat} (hC : ∀ i, C i < 2 ^ 64) (k : Nat) : dbw C k < 2 ^ 64 := by
  unfold dbw cp
  have : C k * 2 % 2 ^ 64 % 2 = 0 := by omega
  have := Nat.mod_lt (C k * 2) (show 0 < 2 ^ 64 by decide)
  split
  · omega
  · have := hC (k - 1)
    have : C (k - 1) / 2 ^ 63 ≤ 1 := by omega
    omega

theorem dq_lt {X : Nat → Nat} (hX : ∀ i, X i < 2 ^ 64) (k : Nat) : dq X k < 2 ^ 64 := by
  unfold dq; split
  · exact Nat.mod_lt _ (by decide)
  · have := nat_mulhi_lt (hX (k / 2)) (hX (k / 2)); omega

/-- The end of step `k`: the carry added, the word stored. -/
theorem dblEnd_ok {s0 : State} {x : Nat} {C : Nat → Nat} (hC : ∀ i, C i < 2 ^ 64) {k : Nat}
    (hk : k < 14) {s s4 : State}
    (h : DblInv b s0 x C k s) (hc4 : Ctx b s4) (hr4 : Rest clob64 s s4) (hm4 : s4.mem = s.mem)
    (h4 : s4.gpr .a4 = s.gpr .a4) (h5 : (s4.gpr .a5).toNat = C k)
    (hv : (s4.gpr .a6).toNat + 2 ^ 64 * (s4.gpr .a7).toNat =
      dbw C k + dq (fun i => dw s0.mem b (x + 8 * i)) k)
    (ht : (k + 1) % 2 = 1 → (s4.gpr .t3).toNat =
      dw s0.mem b (x + 8 * ((k + 1) / 2)) * dw s0.mem b (x + 8 * ((k + 1) / 2)) / 2 ^ 64) :
    WP isa (.block (([.add .a6 .a6 .a4, .sltu .t0 .a6 .a4, .add .a4 .a7 .t0] : List Instr) ++
      ([.store .d .a6 .a3 (ACC + 8 * k)] : List Instr))) s4 (DblInv b s0 x C (k + 1)) := by
  have hA := ACC_eq
  have hb1 := dbw_lt hC k
  have hb2 := dq_lt (X := fun i => dw s0.mem b (x + 8 * i)) (fun i => dw_lt _ _ _) k
  have h7 : (s4.gpr .a7).toNat ≤ 1 := by
    have := (s4.gpr .a6).isLt
    omega
  refine WP.append dbl4_ok fun s5 ⟨e5, k5⟩ => ?_
  have hr5 : Rest clob64 s4 s5 := Rest.mono (ws' := clob64) (Keeps.rest k5) (by decide)
  have hc5 : Ctx b s5 := hc4.of_rest hr5 (by decide)
  refine sd_ok hc5 (by omega) (by omega) fun s6 u6 => WP.block_nil ?_
  have hm6 : s6.mem = s.mem.writeW (b + BitVec.ofNat 64 (ACC + 8 * k)) (s5.gpr .a6) := by
    rw [u6.mem, k5.2.1, hm4]
  have hr6 : Rest clob64 s s6 := hr4.trans (hr5.trans (u6.rest _))
  have e5' := e5 h7
  rw [h4] at e5'
  have hcy := h.cy
  have hv6 : (s6.gpr .a6).toNat + 2 ^ 64 * (s6.gpr .a4).toNat =
      dbw C k + dq (fun i => dw s0.mem b (x + 8 * i)) k + (s.gpr .a4).toNat := by
    rw [u6.gpr]; omega
  refine ⟨hc5.of_rest (u6.rest clob64) (by decide), h.rest.trans hr6, ?_, fun i hi hi' => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm6]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))
  · rw [hm6, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    exact h.hi i (by omega) hi'
  · rw [u6.gpr, k5.1 _ (by decide), h5]; simp
  · intro hk1; rw [u6.gpr, k5.1 _ (by decide)]; exact ht hk1
  · have := (s6.gpr .a6).isLt
    omega
  · have ea : accW s6.mem b k = accW s.mem b k := accW_congr fun c hc' => by
      rw [hm6, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have ek : dw s6.mem b (ACC + 8 * k) = (s5.gpr .a6).toNat := by rw [hm6, dw_write_self]
    rw [accW, ea, ek, colsV, ← h.val, Nat.pow_succ (n := 2 ^ 64)]
    rw [u6.gpr] at hv6 ⊢
    generalize (2 ^ 64) ^ k = K at *
    generalize (s5.gpr .a6).toNat = a at *
    generalize (s5.gpr .a4).toNat = c at *
    generalize (s.gpr .a4).toNat = d at *
    generalize dbw C k + dq (fun i => dw s0.mem b (x + 8 * i)) k = t at *
    generalize 2 ^ 64 = W at *
    grind

theorem dblStep_ok {s0 : State} {x : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) {C : Nat → Nat}
    (hC : ∀ i, C i < 2 ^ 64) {k : Nat} (hk : k < 14) {s : State} (h : DblInv b s0 x C k s) :
    WP isa (.block (dblStep x k)) s (DblInv b s0 x C (k + 1)) := by
  have hA := ACC_eq
  have hc := h.ctx
  have e : dblStep x k = [.shift .srl .d .a7 .a5 63] ++ (.load .d .a5 .a3 (ACC + 8 * k) ::
      ([.shift .sll .d .a6 .a5 1, .logic .or .a6 .a6 .a7] ++
        ((if k % 2 = 0 then
          .load .d .t3 .a3 (x + 8 * (k / 2)) :: [.mul .t0 .t3 .t3, .mulhu .t3 .t3 .t3,
            .add .a6 .a6 .t0, .sltu .a7 .a6 .t0]
         else [.add .a6 .a6 .t3, .sltu .a7 .a6 .t3]) ++
        ([.add .a6 .a6 .a4, .sltu .t0 .a6 .a4, .add .a4 .a7 .t0] ++
          [.store .d .a6 .a3 (ACC + 8 * k)])))) := by
    simp only [dblStep, List.cons_append, List.nil_append]
  rw [e]
  refine WP.append dbl1_ok fun s1 ⟨e1, k1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest (Rest.mono (ws' := clob64) (Keeps.rest k1) (by decide)) (by decide)
  refine ld_ok hc1 (by omega) (by omega) fun s2 u2 => ?_
  refine WP.append dbl2_ok fun s3 ⟨e3, k3⟩ => ?_
  have hck : (s2.gpr .a5).toNat = C k := by
    rw [u2.gpr, show (s1.mem.readW _ 64).toNat = dw s1.mem b (ACC + 8 * k) from rfl, k1.2.1]
    exact h.hi k (Nat.le_refl _) hk
  have hp7 : (s2.gpr .a7).toNat = cp C k := by
    rw [u2.other _ (by decide), e1, h.prev, cp]
    split <;> simp
  have hp1 : (s2.gpr .a7).toNat ≤ 1 := by
    have := (s.gpr .a5).isLt
    rw [u2.other _ (by decide), e1]; omega
  have ha6 : (s3.gpr .a6).toNat = dbw C k := by rw [e3 hp1, hck, hp7]; rfl
  have hm3 : s3.mem = s.mem := by rw [k3.2.1, u2.mem, k1.2.1]
  have hr3 : Rest clob64 s s3 := (Rest.mono (ws' := clob64) (Keeps.rest k1) (by decide)).trans
    ((u2.rest (by decide)).trans (Rest.mono (ws' := clob64) (Keeps.rest k3) (by decide)))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have h4s : s3.gpr .a4 = s.gpr .a4 := by
    rw [k3.1 _ (by decide), u2.other _ (by decide), k1.1 _ (by decide)]
  have h5s : (s3.gpr .a5).toNat = C k := by rw [k3.1 _ (by decide)]; exact hck
  have hk2 : x + 8 * (k / 2) + 8 ≤ ACC := by omega
  by_cases hpar : k % 2 = 0
  · rw [ite_eq_left hpar, List.cons_append]
    refine ld_ok hc3 (by omega) (by omega) fun s4 u4 => ?_
    refine WP.append dbl3e_ok fun s5 ⟨e5, f5, k5⟩ => ?_
    have hr5 : Rest clob64 s3 s5 := (u4.rest (by decide)).trans
      (Rest.mono (ws' := clob64) (Keeps.rest k5) (by decide))
    have ht4 : (s4.gpr .t3).toNat = dw s0.mem b (x + 8 * (k / 2)) := by
      rw [u4.gpr, show (s3.mem.readW _ 64).toNat = dw s3.mem b (x + 8 * (k / 2)) from rfl, hm3]
      exact dw_acc h.frame hk2
    refine dblEnd_ok hC hk h (hc3.of_rest hr5 (by decide)) (hr3.trans hr5)
      (by rw [k5.2.1, u4.mem, hm3]) (by rw [k5.1 _ (by decide), u4.other _ (by decide), h4s])
      (by rw [k5.1 _ (by decide), u4.other _ (by decide), h5s]) ?_ ?_
    · rw [e5, u4.other _ (by decide), ha6, ht4, dq, ite_eq_left hpar]
    · intro _
      rw [f5, ht4, show (k + 1) / 2 = k / 2 by omega]
  · rw [ite_eq_right hpar]
    refine WP.append dbl3o_ok fun s5 ⟨e5, k5⟩ => ?_
    have hr5 : Rest clob64 s3 s5 := Rest.mono (ws' := clob64) (Keeps.rest k5) (by decide)
    have ht3 : (s3.gpr .t3).toNat = dw s0.mem b (x + 8 * (k / 2)) * dw s0.mem b (x + 8 * (k / 2)) / 2 ^ 64 := by
      rw [k3.1 _ (by decide), u2.other _ (by decide), k1.1 _ (by decide)]
      exact h.sqhi (by omega)
    refine dblEnd_ok hC hk h (hc3.of_rest hr5 (by decide)) (hr3.trans hr5)
      (by rw [k5.2.1, hm3]) (by rw [k5.1 _ (by decide), h4s])
      (by rw [k5.1 _ (by decide), h5s]) ?_ (fun h' => absurd h' (by omega))
    rw [e5, ha6, ht3, dq, ite_eq_right hpar]

/-- The steps of the doubling, by induction. -/
theorem dbls_ok {s0 : State} {x : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) {C : Nat → Nat}
    (hC : ∀ i, C i < 2 ^ 64) :
    ∀ n ≤ 14, ∀ s, DblInv b s0 x C 0 s →
      WP isa (.block ((List.range n).flatMap (dblStep x))) s (DblInv b s0 x C n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (dbls_ok hx hx8 hC n (by omega) s h) fun s1 h1 => dblStep_ok hx hx8 hC (by omega) h1

/-- `square x`: the fourteen words of `[x]²` at `ACC`. -/
theorem square_ok {x : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (square x)) s0 fun s' => Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s'.mem ∧
      accW s'.mem b 14 = Proof.X448.RISCV64.V s0.mem b x * Proof.X448.RISCV64.V s0.mem b x := by
  have hA := ACC_eq
  have hX : ∀ i, dw s0.mem b (x + 8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
  unfold square
  simp only [List.append_assoc]
  refine WP.append (ld6_ok (by omega) hx8 hc) fun s1 ⟨h1, hr1, hm1⟩ => ?_
  refine WP.append zero3_ok fun s2 ⟨e4, e5, e6, hr2, hm2⟩ => ?_
  have hr12 := hr1.trans (hr2.mono (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr12 (by decide)
  have hinit : ColInv b s0 (sqCs fun i => dw s0.mem b (x + 8 * i)) 0 s2 :=
    ⟨hc2, hr12, by rw [hm2, hm1]; exact Frame.refl _ _, e6, by
      simp only [accW, colsV, show rr 0 = .a4 from rfl, show rr (0 + 1) = .a5 from rfl, e4, e5]; rfl⟩
  have hA2 : ARegs (fun i => dw s0.mem b (x + 8 * i)) s2 := fun i hi => by
    rw [hr2.gpr _ (by revert hi; revert i; decide), h1 i hi]
  refine WP.append (columns_ok (Inv := fun _ => ARegs fun i => dw s0.mem b (x + 8 * i))
    (fun k hk s h hi => sqCol_ok hx hx8 hk h hi) 14 (Nat.le_refl _) s2 hinit hA2)
    fun s3 ⟨h3, _⟩ => ?_
  have hsum := sqCols_sum fun i => dw s0.mem b (x + 8 * i)
  have hlt : val7 (fun i => dw s0.mem b (x + 8 * i)) * val7 (fun i => dw s0.mem b (x + 8 * i)) <
      (2 ^ 64) ^ 14 := by
    rw [show (14 : Nat) = 7 + 7 from rfl, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (val7_lt fun i _ => hX i) (val7_lt fun i _ => hX i)
  have hfin := h3.final (by omega)
  refine wp_li (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => ?_
  have hr5 : Rest clob64 s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  have hm5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  have hd0 : DblInv b s0 x (fun i => dw s3.mem b (ACC + 8 * i)) 0 s5 :=
    ⟨h3.ctx.of_rest hr5 (by decide), h3.rest.trans hr5, by rw [hm5]; exact h3.frame,
      fun i _ _ => by rw [hm5], by rw [u5.other _ (by decide), u4.gpr]; rfl, fun h' => absurd h' (by decide),
      by rw [u5.gpr]; decide, by rw [u5.gpr]; rfl⟩
  refine WP.mono (dbls_ok hx hx8 (fun i => dw_lt _ _ _) 14 (Nat.le_refl _) s5 hd0) fun s6 h6 =>
    ⟨h6.ctx, h6.rest, h6.frame, ?_⟩
  have hv := h6.val
  rw [colsV_add, colsV_dq] at hv
  have hd := colsV_dbw (C := fun i => dw s3.mem b (ACC + 8 * i)) (fun i => dw_lt _ _ _) 13
  rw [← accW_eq, hfin] at hd
  rw [V_eq]
  have := accW_lt s6.mem b 14
  generalize (2 ^ 64) ^ 14 = K at *
  generalize accW s6.mem b 14 = A at *
  generalize val7 (fun i => dw s0.mem b (x + 8 * i)) * val7 (fun i => dw s0.mem b (x + 8 * i)) = Q at *
  generalize colsV (dbw fun i => dw s3.mem b (ACC + 8 * i)) 14 = D at *
  generalize colsV (sqCs fun i => dw s0.mem b (x + 8 * i)) 14 = S at *
  generalize dsq (fun i => dw s0.mem b (x + 8 * i)) = E at *
  generalize (s6.gpr .a4).toNat = c at *
  generalize dw s3.mem b (ACC + 8 * 13) / 2 ^ 63 = t at *
  rcases Nat.eq_zero_or_pos (c + t) with h0 | hpos
  · have : c = 0 := by omega
    have : t = 0 := by omega
    subst_vars; omega
  · have : K ≤ K * (c + t) := Nat.le_mul_of_pos_right _ hpos
    rw [Nat.mul_add] at this
    omega

end

end

section

open VG VG.RISCV64 VG.Impl.X448.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (ACC)
open VG.Spec.X448 (P)
open VG.Proof.X448.RISCV64 (V)

section
variable {b : Addr}

theorem mul_ok {o x y : Nat} (ho : o + 56 ≤ ACC) (hx : x + 56 ≤ ACC) (hy : y + 56 ≤ ACC)
    (ho8 : o % 8 = 0) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) {s : State} (hc : Ctx b s) :
    WP isa (mul o x y) s fun s' =>
      Rest clob64 s s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := by
  have fin : ∀ s1, Ctx b s1 → Rest clob64 s s1 →
      Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem s1.mem →
      accW s1.mem b 14 = V s.mem b x * V s.mem b y →
      WP isa (.block (reduce o)) s1 fun s' =>
        Rest clob64 s s' ∧
        Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem s'.mem ∧
        V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := fun s1 hc1 hr1 hf1 ha1 =>
    WP.mono (reduce_ok ho ho8 hc1) fun s' ⟨_, hr2, hf2, hv2⟩ =>
      ⟨hr1.trans hr2, (hf1.mono (by simp)).trans (hf2.mono (by simp)), by rw [hv2, ha1]⟩
  unfold mul
  by_cases hxy : x = y
  · subst hxy
    rw [ite_eq_left rfl]
    exact WP.append (square_ok hx hx8 hc) fun s1 ⟨hc1, hr1, hf1, ha1⟩ => fin s1 hc1 hr1 hf1 ha1
  · rw [ite_eq_right hxy]
    exact WP.append (product_ok hx hx8 hy hy8 hc) fun s1 ⟨hc1, hr1, hf1, ha1⟩ => fin s1 hc1 hr1 hf1 ha1

end

end

end VG.Proof.X448.RISCV64.R64
