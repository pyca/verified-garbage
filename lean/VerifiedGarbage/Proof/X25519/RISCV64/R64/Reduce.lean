module

public import VerifiedGarbage.Proof.X25519.RISCV64.R64.Mul
import VerifiedGarbage.Proof.X448.RISCV64.R64.AddSub
import VerifiedGarbage.Proof.X448.RISCV64.R64.Carry
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Reduce

/-!
# X25519 on RISC-V, 64-bit limbs: the field operations

* `reduce acc o` (`reduce_ok`): the product `L + 2²⁵⁶ H` at `acc` becomes the
  four words of `L + 38 H` (`redT`, congruent to it: `redT_mod`), word `k`
  with the high word of `38 H_{k-1}` and the carries in (`redStep_ok`, the
  invariant `RedInv`); then the carry out `c ≤ 40` is folded in as `38 c`
  twice (`fold_ok`, `fold_twice`) and the words stored (`st4_ok`).
* `mulAt acc o x y` (`mulAt_ok`): the product or the square
  (`Proof/X25519/RISCV64/R64/Mul.lean`), then its reduction.
* `add o x y` (`add_ok`) and `sub o x y` (`sub_ok`): the words with carries
  (borrows), as X448's are (`addSteps_ok`, `subSteps_ok`), then the carry
  folded in (the borrow taken out, `unfold_ok`) as 38, twice.
-/

-- separate module: its proofs (about 3 s) cost more than its imports, and its importer's
-- changes need not re-check them

@[expose] public section

namespace VG.Proof.X25519.RISCV64.R64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.X25519.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64.R64 (w addStep subStep)
open VG.Proof.X448.RISCV64.R64 (clob64 dw dw_lt ew ld_ok sd_ok dw_write_self dw_write_other colsV
  Keeps.rest addOut_ok subOut_ok addSmall_ok Keeps.rest_mono_of_upd addc_ok regsV colsV_congr AddInv
  SubInv addSteps_ok subSteps_ok)
open VG.Spec.X25519 (P)

variable {s : State}

/-! ## Folds -/

set_option linter.unusedSimpArgs false in
/-- `d := a · b` without wrapping. -/
theorem mulSmall_ok {d a b : Reg} :
    WP isa (.block [.mul d a b]) s fun s' =>
      ((s.gpr a).toNat * (s.gpr b).toNat < 2 ^ 64 →
        (s'.gpr d).toNat = (s.gpr a).toNat * (s.gpr b).toNat) ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mul, RegUpd.gpr_write, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun h => by rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h], fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [RegUpd.gpr_write, hx, ite_false]

/-- The four words in `w 0`–`w 3`. -/
abbrev rw4 (s : State) : Nat := val4 fun i => (s.gpr (w i)).toNat

theorem fold_eq : fold =
    ([.mul .a7 .a5 .a4] : List Instr) ++
    (([.add (w 0) (w 0) .a7, .sltu .t0 (w 0) .a7] : List Instr) ++
    (([.add (w 1) (w 1) .t0, .sltu .t0 (w 1) .t0] : List Instr) ++
    (([.add (w 2) (w 2) .t0, .sltu .t0 (w 2) .t0] : List Instr) ++
    (([.add (w 3) (w 3) .t0, .sltu .a5 (w 3) .t0] : List Instr))))) := rfl

/-- `fold`: the four words plus `38 c`, for `c < 2⁵⁸` in `a5` and 38 in
`a4`, the carry out in `a5`. -/
theorem fold_ok (h4 : s.gpr .a4 = 38) :
    WP isa (.block fold) s fun s' =>
      ((s.gpr .a5).toNat < 2 ^ 58 →
        rw4 s' + 2 ^ 256 * (s'.gpr .a5).toNat = rw4 s + 38 * (s.gpr .a5).toNat) ∧
      Keeps [.t3, .t4, .t5, .t6, .a5, .a7, .t0] s s' := by
  rw [fold_eq]
  refine WP.append mulSmall_ok fun s1 ⟨e1, k1⟩ => ?_
  refine WP.append (addOut_ok (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  refine WP.append (addOut_ok (by decide) (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.append (addOut_ok (by decide) (by decide)) fun s4 ⟨e4, k4⟩ => ?_
  refine WP.mono (addOut_ok (by decide) (by decide)) fun s5 ⟨e5, k5⟩ => ⟨fun hc => ?_, ?_⟩
  · have t38 : (s.gpr .a4).toNat = 38 := by rw [h4]; rfl
    have e1 := e1 (by rw [t38]; omega)
    rw [t38] at e1
    have l1 : s5.gpr (w 0) = s2.gpr (w 0) := by
      rw [k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide)]
    have l2 : s5.gpr (w 1) = s3.gpr (w 1) := by rw [k5.1 _ (by decide), k4.1 _ (by decide)]
    have l3 : s5.gpr (w 2) = s4.gpr (w 2) := by rw [k5.1 _ (by decide)]
    have r0 : s1.gpr (w 0) = s.gpr (w 0) := k1.1 _ (by decide)
    have r1 : s2.gpr (w 1) = s.gpr (w 1) := by rw [k2.1 _ (by decide), k1.1 _ (by decide)]
    have r2 : s3.gpr (w 2) = s.gpr (w 2) := by
      rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    have r3 : s4.gpr (w 3) = s.gpr (w 3) := by
      rw [k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    rw [r0] at e2; rw [r1] at e3; rw [r2] at e4; rw [r3] at e5
    rw [e1] at e2
    simp only [rw4, val4, l1, l2, l3]
    have hb : ∀ (x : State) (r : Reg), (x.gpr r).toNat < 2 ^ 64 := fun x r => (x.gpr r).isLt
    have := hb s2 .t0; have := hb s3 .t0; have := hb s4 .t0; have := hb s5 .a5
    have := hb s2 (w 0); have := hb s3 (w 1); have := hb s4 (w 2); have := hb s5 (w 3)
    have := hb s (w 0); have := hb s (w 1); have := hb s (w 2); have := hb s (w 3)
    omega
  · exact ((((k1.trans k2).trans k3).trans k4).trans k5).mono (by decide)

theorem unfold_eq : unfold =
    ([.mul .a7 .a5 .a4] : List Instr) ++
    (([.sltu .t0 (w 0) .a7, .sub (w 0) (w 0) .a7] : List Instr) ++
    (([.sltu .a7 (w 1) .t0, .sub (w 1) (w 1) .t0] : List Instr) ++
    (([.sltu .t0 (w 2) .a7, .sub (w 2) (w 2) .a7] : List Instr) ++
    (([.sltu .a5 (w 3) .t0, .sub (w 3) (w 3) .t0] : List Instr))))) := rfl

/-- `unfold`: the four words less `38 c`, for `c < 2⁵⁸` in `a5` and 38 in
`a4`, the borrow out in `a5`. -/
theorem unfold_ok (h4 : s.gpr .a4 = 38) :
    WP isa (.block unfold) s fun s' =>
      ((s.gpr .a5).toNat < 2 ^ 58 →
        rw4 s' + 38 * (s.gpr .a5).toNat = rw4 s + 2 ^ 256 * (s'.gpr .a5).toNat) ∧
      Keeps [.t3, .t4, .t5, .t6, .a5, .a7, .t0] s s' := by
  rw [unfold_eq]
  refine WP.append mulSmall_ok fun s1 ⟨e1, k1⟩ => ?_
  refine WP.append (subOut_ok (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  refine WP.append (subOut_ok (by decide) (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.append (subOut_ok (by decide) (by decide)) fun s4 ⟨e4, k4⟩ => ?_
  refine WP.mono (subOut_ok (by decide) (by decide)) fun s5 ⟨e5, k5⟩ => ⟨fun hc => ?_, ?_⟩
  · have t38 : (s.gpr .a4).toNat = 38 := by rw [h4]; rfl
    have e1 := e1 (by rw [t38]; omega)
    rw [t38] at e1
    have l1 : s5.gpr (w 0) = s2.gpr (w 0) := by
      rw [k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide)]
    have l2 : s5.gpr (w 1) = s3.gpr (w 1) := by rw [k5.1 _ (by decide), k4.1 _ (by decide)]
    have l3 : s5.gpr (w 2) = s4.gpr (w 2) := by rw [k5.1 _ (by decide)]
    have r0 : s1.gpr (w 0) = s.gpr (w 0) := k1.1 _ (by decide)
    have r1 : s2.gpr (w 1) = s.gpr (w 1) := by rw [k2.1 _ (by decide), k1.1 _ (by decide)]
    have r2 : s3.gpr (w 2) = s.gpr (w 2) := by
      rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    have r3 : s4.gpr (w 3) = s.gpr (w 3) := by
      rw [k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    rw [r0] at e2; rw [r1] at e3; rw [r2] at e4; rw [r3] at e5
    rw [e1] at e2
    simp only [rw4, val4, l1, l2, l3]
    have hb : ∀ (x : State) (r : Reg), (x.gpr r).toNat < 2 ^ 64 := fun x r => (x.gpr r).isLt
    have := hb s2 .t0; have := hb s3 .a7; have := hb s4 .t0; have := hb s5 .a5
    have := hb s2 (w 0); have := hb s3 (w 1); have := hb s4 (w 2); have := hb s5 (w 3)
    have := hb s (w 0); have := hb s (w 1); have := hb s (w 2); have := hb s (w 3)
    omega
  · exact ((((k1.trans k2).trans k3).trans k4).trans k5).mono (by decide)

theorem B4_eq : ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 := by rw [← Nat.pow_mul]

/-- Two folds of a carry `c ≤ 40` leave a number congruent to `v₁ + 2²⁵⁶ c`. -/
theorem fold_twice {v1 v2 v3 c c2 c3 : Nat} (hv2 : v2 < 2 ^ 256) (hv3 : v3 < 2 ^ 256) (hc : c ≤ 40)
    (e2 : v2 + 2 ^ 256 * c2 = v1 + 38 * c) (e3 : v3 + 2 ^ 256 * c3 = v2 + 38 * c2)
    (hv1 : v1 < 2 ^ 256) : v3 % P = (v1 + 2 ^ 256 * c) % P := by
  have hc2 : c2 ≤ 1 := by omega
  have hc3 : c3 = 0 := by omega
  subst hc3
  rw [fold256, show v1 + 38 * c = v2 + 2 ^ 256 * c2 by omega, fold256]
  congr 1

/-- Two borrows `c ≤ 1` taken out leave a number congruent to `x - y`. -/
theorem unfold_twice {v0 v1 v2 X Y c c1 c2 : Nat} (hv0 : v0 < 2 ^ 256) (hv1 : v1 < 2 ^ 256)
    (hv2 : v2 < 2 ^ 256) (hc : c ≤ 1) (e0 : v0 + Y = X + 2 ^ 256 * c)
    (e1 : v1 + 38 * c = v0 + 2 ^ 256 * c1) (e2 : v2 + 38 * c1 = v1 + 2 ^ 256 * c2) :
    (v2 + Y) % P = X % P := by
  have hc1 : c1 ≤ 1 := by omega
  have hc2 : c2 = 0 := by omega
  subst hc2
  have : v2 + Y = X + P * (2 * (c + c1)) := by
    simp only [P]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with rfl | rfl <;> omega
  rw [this, Nat.add_mul_mod_self_left]

/-! ## Storing the words -/

section
variable {b : Addr}

/-- `w 0`, …, `w (n - 1)` stored at `[o]`. -/
theorem sts_ok {o : Nat} (ho : o + 32 ≤ 2048) (ho8 : o % 8 = 0) :
    ∀ n ≤ 4, ∀ s, Ctx b s →
      WP isa (.block ((List.range n).map fun i => .store .d (w i) .a3 (o + 8 * i))) s fun s' =>
        (∀ i < n, dw s'.mem b (o + 8 * i) = (s.gpr (w i)).toNat) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem
  | 0, _, s, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn, s, hc => by
    rw [List.range_succ, List.map_append]
    refine WP.append (sts_ok ho ho8 n (by omega) s hc) fun s1 ⟨h1, g1, r1, w1, p1, f1⟩ => ?_
    have hc1 : Ctx b s1 := ⟨by rw [g1, hc.a3], hc.al, by rw [w1]; exact hc.wr⟩
    refine sd_ok hc1 (by omega) (by omega) fun s2 u2 => WP.block_nil ⟨fun i hi => ?_,
      by rw [u2.gpr, g1], by rw [u2.rd, r1], by rw [u2.wr, w1], by rw [u2.sp, p1], ?_⟩
    · rw [u2.mem]
      by_cases hin : i = n
      · subst hin; rw [dw_write_self, g1]
      · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h1 i (by omega)
    · rw [u2.mem]
      exact f1.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))

/-- `st4 o`, then the element at `o` is the four words. -/
theorem st4_ok {o : Nat} (ho : o + 32 ≤ 2048) (ho8 : o % 8 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (st4 o)) s fun s' => Ctx b s' ∧ Rest [] s s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧ V s'.mem b o = rw4 s :=
  WP.mono (sts_ok ho ho8 4 (Nat.le_refl _) s hc) fun s' ⟨h4, g4, r4, w4, p4, f4⟩ =>
    ⟨⟨by rw [g4, hc.a3], hc.al, by rw [w4]; exact hc.wr⟩, ⟨fun r _ => by rw [g4], r4, w4, p4⟩, f4,
      by rw [V_eq4]; exact val4_congr fun i hi => h4 i hi⟩

end

/-! ## The reduction -/

/-- Word `k` of `L + 38 H`, for the product's words `Pw`. -/
def redT (Pw : Nat → Nat) (k : Nat) : Nat := Pw k + 38 * Pw (4 + k)

/-- `2²⁵⁶ H ≡ 38 H` modulo `p`. -/
theorem redT_mod (Pw : Nat → Nat) : colsV (redT Pw) 4 % P = colsV Pw 8 % P := by
  have e : colsV Pw 8 = colsV Pw 4 + 2 ^ 256 * colsV (fun k => Pw (4 + k)) 4 := by
    rw [← B4_eq]
    simp only [colsV, Nat.reduceAdd]
    generalize 2 ^ 64 = B
    grind
  have e' : colsV (redT Pw) 4 = colsV Pw 4 + 38 * colsV (fun k => Pw (4 + k)) 4 := by
    simp only [colsV, redT, Nat.reduceAdd]
    generalize 2 ^ 64 = B
    grind
  rw [e, e', fold256]

/-- The carry into word `k` of the reduction (none for word 0): the high
word of `38 H_{k-1}` and the carry out of word `k - 1`. -/
def cv (k : Nat) (s : State) : Nat :=
  if k = 0 then 0 else (s.gpr (hr (k + 1))).toNat + (s.gpr (cr (k + 1))).toNat

section
variable {b : Addr}

/-- Before word `k` of the reduction, from `sp` (the product at `acc`): 38 in
`a4`, the words below `k` and the carry the first `k` words of `redT`. -/
structure RedInv (acc : Nat) (b : Addr) (sp : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 sp s
  mem : s.mem = sp.mem
  a4 : s.gpr .a4 = 38
  val : colsV (regsV s) k + (2 ^ 64) ^ k * cv k s = colsV (redT fun i => dw sp.mem b (acc + 8 * i)) k
  cy : cv k s ≤ 40

theorem red_regs : ∀ k < 4, w k ≠ .a7 ∧ w k ≠ .t0 ∧ w k ≠ .a4 ∧ hr k ≠ .a7 ∧ hr k ≠ .t0 ∧
    hr k ≠ .a4 ∧ hr k ≠ w k ∧ cr k ≠ .a7 ∧ cr k ≠ .t0 ∧ cr k ≠ .a4 ∧ cr k ≠ w k ∧ cr k ≠ hr k ∧
    hr (k + 2) = hr k ∧ cr (k + 2) = cr k ∧ w k ∈ clob64 ∧ hr k ∈ clob64 ∧ cr k ∈ clob64 := by
  decide

theorem red_regs' : ∀ k < 4, hr (k + 1) ≠ w k ∧ hr (k + 1) ≠ .a7 ∧ hr (k + 1) ≠ .t0 ∧
    hr (k + 1) ≠ hr k ∧ hr (k + 1) ≠ cr k ∧ cr (k + 1) ≠ w k ∧ cr (k + 1) ≠ .a7 ∧
    cr (k + 1) ≠ .t0 ∧ cr (k + 1) ≠ hr k ∧ cr (k + 1) ≠ cr k := by decide

theorem red_below' : ∀ k ∈ List.range 4, ∀ c ∈ List.range k,
    w c ≠ w k ∧ w c ≠ hr k ∧ w c ≠ cr k ∧ w c ≠ .a7 ∧ w c ≠ .t0 := by decide

theorem red_below {k c : Nat} (hk : k < 4) (hc : c < k) :
    w c ≠ w k ∧ w c ≠ hr k ∧ w c ≠ cr k ∧ w c ≠ .a7 ∧ w c ≠ .t0 :=
  red_below' k (List.mem_range.mpr hk) c (List.mem_range.mpr hc)

/-- The end of word `k`: the invariant for `k + 1`. -/
theorem redFinish {acc : Nat} {sp : State} {k : Nat} (hk : k < 4) {s s' : State}
    (h : RedInv acc b sp k s) (hkp : Keeps [w k, .a7, .t0, hr k, cr k] s s')
    (hv : (s'.gpr (w k)).toNat + 2 ^ 64 * ((s'.gpr (cr k)).toNat + (s'.gpr (hr k)).toNat) =
      redT (fun i => dw sp.mem b (acc + 8 * i)) k + cv k s)
    (hhr : (s'.gpr (hr k)).toNat ≤ 37) (hcr : (s'.gpr (cr k)).toNat ≤ 3) :
    RedInv acc b sp (k + 1) s' := by
  obtain ⟨h7, h0, h4, -, -, r4, -, -, -, c4, -, -, hh2, hc2, wc, hc, cc⟩ := red_regs k hk
  have hwc : ∀ c < k, s'.gpr (w c) = s.gpr (w c) := fun c hc' => by
    obtain ⟨n1, n2, n3, n4, n5⟩ := red_below hk hc'
    rw [hkp.1 _ (by simp [n1, n2, n3, n4, n5])]
  have hrs : Rest clob64 s s' := Rest.mono (Keeps.rest hkp) fun r hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    exacts [wc, by decide, by decide, hc, cc]
  have hcv : cv (k + 1) s' = (s'.gpr (hr k)).toNat + (s'.gpr (cr k)).toNat := by
    simp only [cv, show k + 1 ≠ 0 by omega, ite_false, show k + 1 + 1 = k + 2 by omega, hh2, hc2]
  refine ⟨h.ctx.of_rest hrs (by decide), h.rest.trans hrs, by rw [hkp.2.1, h.mem],
    by rw [hkp.1 _ (by simp [Ne.symm h4, Ne.symm r4, Ne.symm c4]), h.a4], ?_, by rw [hcv]; omega⟩
  rw [hcv, colsV, colsV, colsV_congr (g := regsV s) fun c hc => by simp only [regsV, hwc c hc],
    ← h.val, Nat.pow_succ (n := 2 ^ 64)]
  simp only [regsV] at hv ⊢
  generalize (2 ^ 64) ^ k = K
  generalize colsV (fun c => (s.gpr (w c)).toNat) k = A
  generalize (s'.gpr (w k)).toNat = a at hv
  generalize (s'.gpr (cr k)).toNat = c at hv
  generalize (s'.gpr (hr k)).toNat = d at hv
  generalize cv k s = e at hv
  generalize redT (fun i => dw sp.mem b (acc + 8 * i)) k = t at hv
  have : K * a + K * 2 ^ 64 * (d + c) = K * (t + e) := by
    rw [Nat.mul_assoc, ← Nat.mul_add, ← hv]; congr 1; omega
  simp only [Nat.mul_add] at this ⊢
  omega

theorem redStep_ok {acc : Nat} (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0) {sp : State} {k : Nat}
    (hk : k < 4) (h : RedInv acc b sp k s) :
    WP isa (.block (redStep acc k)) s (RedInv acc b sp (k + 1)) := by
  obtain ⟨h7, h0, h4, r7, r0, r4, rw', c7, c0, c4, cw, ch, -, -, wc, hc, cc⟩ := red_regs k hk
  obtain ⟨dw', d7, d0, dh, dc, ew', e7, e0, eh, ec⟩ := red_regs' k hk
  have hcx := h.ctx
  have e : redStep acc k = .load .d (w k) .a3 (acc + 8 * k) ::
      .load .d .a7 .a3 (acc + 32 + 8 * k) :: (Impl.Words.RISCV64.mulWide .t0 (hr k) .a7 .a4 ++
      ([.add (w k) (w k) .t0, .sltu (cr k) (w k) .t0] ++
      (if 0 < k then [.add (w k) (w k) (hr (k + 1)), .sltu .a7 (w k) (hr (k + 1)), .add (cr k) (cr k) .a7] ++
        [.add (w k) (w k) (cr (k + 1)), .sltu .a7 (w k) (cr (k + 1)), .add (cr k) (cr k) .a7]
       else []))) := by
    simp only [redStep, Impl.Words.RISCV64.mulWide, List.cons_append, List.nil_append]
  rw [e]
  refine ld_ok hcx (by omega) (by omega) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hcx.of_rest (u1.rest wc) (by decide)
  refine ld_ok hc1 (by omega) (by omega) fun s2 u2 => ?_
  refine WP.append (mulWide_ok (by decide) (by decide) (Ne.symm r0)) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.append (addOut_ok h0 (Ne.symm cw)) fun s4 ⟨e4, k4⟩ => ?_
  have v1 : (s1.gpr (w k)).toNat = dw sp.mem b (acc + 8 * k) := by rw [u1.gpr, h.mem]; rfl
  have v2 : (s2.gpr .a7).toNat = dw sp.mem b (acc + 8 * (4 + k)) := by
    rw [u2.gpr, u1.mem, h.mem, show acc + 32 + 8 * k = acc + 8 * (4 + k) by omega]; rfl
  have v4 : (s2.gpr .a4).toNat = 38 := by
    rw [u2.other _ (by decide), u1.other _ (Ne.symm h4), h.a4]; rfl
  rw [v2, v4] at e3
  have w3 : s3.gpr (w k) = s2.gpr (w k) := k3.1 _ (by simp [h0, Ne.symm rw'])
  rw [w3, u2.other _ h7, v1] at e4
  have t4 : s4.gpr (hr k) = s3.gpr (hr k) := k4.1 _ (by simp [rw', Ne.symm ch])
  have hhr : (s3.gpr (hr k)).toNat ≤ 37 := by
    have := dw_lt sp.mem b (acc + 8 * (4 + k)); omega
  have kp4 : Keeps [w k, .a7, .t0, hr k, cr k] s s4 :=
    ((((Keeps.rest_mono_of_upd u1).trans (Keeps.rest_mono_of_upd u2)).trans k3).trans k4).mono
      fun r hr' => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
        grind
  have hm := h.cy
  have := dw_lt sp.mem b (acc + 8 * k)
  have := (s3.gpr .t0).isLt
  have := (s4.gpr (w k)).isLt
  by_cases k0 : k = 0
  · subst k0
    rw [ite_eq_right (Nat.lt_irrefl 0)]
    refine WP.block_nil (redFinish hk h kp4 ?_ (by rw [t4]; exact hhr) (by omega))
    simp only [cv, redT, ite_true, Nat.add_zero, Nat.mul_zero] at e3 e4 ⊢
    rw [t4]; omega
  · rw [ite_eq_left (Nat.pos_of_ne_zero k0)]
    have i1 : s4.gpr (hr (k + 1)) = s.gpr (hr (k + 1)) := kp4.1 _ (by simp [dw', d7, d0, dh, dc])
    have i2 : s4.gpr (cr (k + 1)) = s.gpr (cr (k + 1)) := kp4.1 _ (by simp [ew', e7, e0, eh, ec])
    have hcv : cv k s = (s.gpr (hr (k + 1))).toNat + (s.gpr (cr (k + 1))).toNat := by
      simp only [cv, k0, ite_false]
    refine WP.append (addc_ok (Ne.symm dw') h7 c7 cw) fun s5 ⟨e5, k5⟩ => ?_
    refine WP.mono (addc_ok (Ne.symm ew') h7 c7 cw) fun s6 ⟨e6, k6⟩ => ?_
    have c4 : (s4.gpr (cr k)).toNat ≤ 1 := by omega
    have e5 := e5 (by omega)
    rw [i1] at e5
    have j5 : s5.gpr (cr (k + 1)) = s.gpr (cr (k + 1)) := by
      rw [k5.1 _ (by simp [ew', e7, ec]), i2]
    have c5 : (s5.gpr (cr k)).toNat ≤ 2 := by
      have := (s5.gpr (w k)).isLt; have := (s.gpr (hr (k + 1))).isLt
      have : (s.gpr (hr (k + 1))).toNat ≤ 40 := by omega
      omega
    have e6 := e6 (by omega)
    rw [j5] at e6
    have t6 : s6.gpr (hr k) = s4.gpr (hr k) := by
      rw [k6.1 _ (by simp [rw', r7, Ne.symm ch]), k5.1 _ (by simp [rw', r7, Ne.symm ch])]
    have hb6 := (s6.gpr (w k)).isLt
    have hb5 := (s5.gpr (w k)).isLt
    refine redFinish hk h ((kp4.trans (k5.trans k6)).mono fun r hr' => ?_) ?_ (by rw [t6, t4]; exact hhr)
      ?_
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
      grind
    · rw [t6, t4, hcv]; simp only [redT]; omega
    · have : (s.gpr (cr (k + 1))).toNat ≤ 40 := by omega
      omega

theorem reds_ok {acc : Nat} (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0) {sp : State} :
    ∀ n ≤ 4, ∀ s, RedInv acc b sp 0 s →
      WP isa (.block ((List.range n).flatMap (redStep acc))) s (RedInv acc b sp n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (reds_ok hA hA8 n (by omega) s h) fun s1 h1 => redStep_ok hA hA8 (by omega) h1

theorem colsV4 (f : Nat → Nat) : colsV f 4 = val4 f := by
  simp only [colsV, val4]
  generalize 2 ^ 64 = B
  grind

/-- `reduce acc o`: the product at `acc` reduced into `[o]`. -/
theorem reduce_ok {acc o : Nat} (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0) (ho : o + 32 ≤ 2048)
    (ho8 : o % 8 = 0) {sp : State} (hc : Ctx b sp) :
    WP isa (.block (reduce acc o)) sp fun s' => Ctx b s' ∧ Rest clob64 sp s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 32⟩] sp.mem s'.mem ∧
      V s'.mem b o % P = accW acc sp.mem b 8 % P := by
  unfold reduce
  simp only [List.cons_append, List.append_assoc]
  refine wp_li (by decide) fun s0 u0 => ?_
  have h0 : RedInv acc b sp 0 s0 := ⟨hc.of_rest (u0.rest (ws := clob64) (by decide)) (by decide),
    u0.rest (by decide), u0.mem, u0.gpr, by simp [colsV, cv], by simp [cv]⟩
  refine WP.append (reds_ok hA hA8 4 (Nat.le_refl _) s0 h0) fun s1 h1 => ?_
  have hcv : cv 4 s1 = (s1.gpr .a2).toNat + (s1.gpr .a6).toNat := rfl
  have hv1 := h1.val
  rw [colsV4] at hv1
  have hcy := h1.cy
  rw [hcv] at hcy hv1
  refine WP.append addSmall_ok fun s2 ⟨e2, k2⟩ => ?_
  have e2 := e2 (by omega)
  have a42 : s2.gpr .a4 = 38 := by rw [k2.1 _ (by decide), h1.a4]
  refine WP.append (fold_ok a42) fun s3 ⟨e3, k3⟩ => ?_
  have e3 := e3 (by omega)
  have a43 : s3.gpr .a4 = 38 := by rw [k3.1 _ (by decide), a42]
  refine WP.append (fold_ok a43) fun s4 ⟨e4, k4⟩ => ?_
  have hl : ∀ v : State, rw4 v < 2 ^ 256 := fun v => by
    rw [← B4_eq]; exact val4_lt fun i _ => (v.gpr (w i)).isLt
  have hc3 : (s3.gpr .a5).toNat ≤ 1 := by
    have := hl s2; have := hl s3; omega
  have e4 := e4 (by omega)
  have hr4 : Rest clob64 sp s4 := h1.rest.trans
    (Rest.mono (Keeps.rest ((k2.trans k3).trans k4)) (by decide))
  have hc4 : Ctx b s4 := hc.of_rest hr4 (by decide)
  have hm4 : s4.mem = sp.mem := by rw [k4.2.1, k3.2.1, k2.2.1, h1.mem]
  refine WP.mono (st4_ok ho ho8 hc4) fun s5 ⟨hc5, hr5, f5, hV⟩ =>
    ⟨hc5, hr4.trans (hr5.mono (by decide)), by rw [← hm4]; exact f5, ?_⟩
  rw [hV]
  have hmod := redT_mod (fun i => dw sp.mem b (acc + 8 * i))
  rw [← accW_eq] at hmod
  have w2 : rw4 s2 = rw4 s1 := by
    simp only [rw4, val4, k2.1 (w 0) (by decide), k2.1 (w 1) (by decide), k2.1 (w 2) (by decide),
      k2.1 (w 3) (by decide)]
  rw [w2, e2] at e3
  rw [← hmod, ← hv1, B4_eq]
  exact fold_twice (hl s3) (hl s4) (by omega) e3 e4 (hl s1)

/-! ## A product -/

theorem mulAt_ok {acc o x y : Nat} (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0) (ho : o + 32 ≤ acc)
    (hx : x + 32 ≤ acc) (hy : y + 32 ≤ acc) (ho8 : o % 8 = 0) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0)
    {s : State} (hc : Ctx b s) :
    WP isa (mulAt acc o x y) s fun s' =>
      Rest clob64 s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩, AR acc b] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := by
  have fin : ∀ s1, Ctx b s1 → Rest clob64 s s1 → Frame [AR acc b] s.mem s1.mem →
      accW acc s1.mem b 8 = V s.mem b x * V s.mem b y →
      WP isa (.block (reduce acc o)) s1 fun s' =>
        Rest clob64 s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩, AR acc b] s.mem s'.mem ∧
        V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := fun s1 hc1 hr1 hf1 ha1 =>
    WP.mono (reduce_ok hA hA8 (by omega) ho8 hc1) fun s' ⟨_, hr2, hf2, hv2⟩ =>
      ⟨hr1.trans hr2, (hf1.mono (by simp)).trans (hf2.mono (by simp)), by rw [hv2, ha1]⟩
  unfold mulAt
  by_cases hxy : x = y
  · subst hxy
    rw [ite_eq_left rfl]
    exact WP.append (square_ok hx hA hA8 hx8 hc) fun s1 ⟨hc1, hr1, hf1, ha1⟩ => fin s1 hc1 hr1 hf1 ha1
  · rw [ite_eq_right hxy]
    exact WP.append (product_ok hx hy hA hA8 hx8 hy8 hc) fun s1 ⟨hc1, hr1, hf1, ha1⟩ =>
      fin s1 hc1 hr1 hf1 ha1

/-! ## Sums and differences -/

theorem add_ok {o x y : Nat} (ho : o + 32 ≤ 2048) (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048)
    (ho8 : o % 8 = 0) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (add o x y)) s fun s' =>
      Rest clob64 s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x + V s.mem b y) % P := by
  unfold add
  simp only [List.append_assoc, List.cons_append]
  refine WP.append (addSteps_ok hx hx8 hy hy8 hc 4 (by decide) (by decide)) fun s1 h1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  have hv1 := h1.val
  have hcy := h1.cy
  rw [colsV4, colsV4, colsV4, B4_eq] at hv1
  have a42 : s2.gpr .a4 = 38 := u2.gpr
  have c2 : s2.gpr .a5 = s1.gpr .a5 := u2.other _ (by decide)
  have w2 : rw4 s2 = val4 (regsV s1) := by
    simp only [rw4, val4, regsV, u2.other (w 0) (by decide), u2.other (w 1) (by decide),
      u2.other (w 2) (by decide), u2.other (w 3) (by decide)]
  refine WP.append (fold_ok a42) fun s3 ⟨e3, k3⟩ => ?_
  have e3 := e3 (by rw [c2]; omega)
  have a43 : s3.gpr .a4 = 38 := by rw [k3.1 _ (by decide), a42]
  refine WP.append (fold_ok a43) fun s4 ⟨e4, k4⟩ => ?_
  have hl : ∀ v : State, rw4 v < 2 ^ 256 := fun v => by
    rw [← B4_eq]; exact val4_lt fun i _ => (v.gpr (w i)).isLt
  have hc3 : (s3.gpr .a5).toNat ≤ 1 := by have := hl s3; have := hl s2; rw [c2] at e3; omega
  have e4 := e4 (by omega)
  have hr4 : Rest clob64 s s4 := h1.rest.trans ((u2.rest (by decide)).trans
    (Rest.mono (Keeps.rest (k3.trans k4)) (by decide)))
  have hc4 : Ctx b s4 := hc.of_rest hr4 (by decide)
  have hm4 : s4.mem = s.mem := by rw [k4.2.1, k3.2.1, u2.mem, h1.mem]
  refine WP.mono (st4_ok ho ho8 hc4) fun s5 ⟨hc5, hr5, f5, hV⟩ =>
    ⟨hr4.trans (hr5.mono (by decide)), by rw [← hm4]; exact f5, ?_⟩
  rw [hV, V_eq4, V_eq4]
  rw [w2, c2] at e3
  have hv0 := hl s2
  rw [w2] at hv0
  have hf := fold_twice (hl s3) (hl s4) (by omega) e3 e4 hv0
  rw [hf, hv1]

theorem sub_ok {o x y : Nat} (ho : o + 32 ≤ 2048) (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048)
    (ho8 : o % 8 = 0) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (sub o x y)) s fun s' =>
      Rest clob64 s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      (V s'.mem b o + V s.mem b y) % P = V s.mem b x % P := by
  unfold sub
  simp only [List.append_assoc, List.cons_append]
  refine WP.append (subSteps_ok hx hx8 hy hy8 hc 4 (by decide) (by decide)) fun s1 h1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  have hv1 := h1.val
  have hcy := h1.cy
  rw [colsV4, colsV4, colsV4, B4_eq] at hv1
  have a42 : s2.gpr .a4 = 38 := u2.gpr
  have c2 : s2.gpr .a5 = s1.gpr .a5 := u2.other _ (by decide)
  have w2 : rw4 s2 = val4 (regsV s1) := by
    simp only [rw4, val4, regsV, u2.other (w 0) (by decide), u2.other (w 1) (by decide),
      u2.other (w 2) (by decide), u2.other (w 3) (by decide)]
  refine WP.append (unfold_ok a42) fun s3 ⟨e3, k3⟩ => ?_
  have e3 := e3 (by rw [c2]; omega)
  have a43 : s3.gpr .a4 = 38 := by rw [k3.1 _ (by decide), a42]
  refine WP.append (unfold_ok a43) fun s4 ⟨e4, k4⟩ => ?_
  have hl : ∀ v : State, rw4 v < 2 ^ 256 := fun v => by
    rw [← B4_eq]; exact val4_lt fun i _ => (v.gpr (w i)).isLt
  have hc3 : (s3.gpr .a5).toNat ≤ 1 := by have := hl s3; have := hl s2; rw [c2] at e3; omega
  have e4 := e4 (by omega)
  have hr4 : Rest clob64 s s4 := h1.rest.trans ((u2.rest (by decide)).trans
    (Rest.mono (Keeps.rest (k3.trans k4)) (by decide)))
  have hc4 : Ctx b s4 := hc.of_rest hr4 (by decide)
  have hm4 : s4.mem = s.mem := by rw [k4.2.1, k3.2.1, u2.mem, h1.mem]
  refine WP.mono (st4_ok ho ho8 hc4) fun s5 ⟨hc5, hr5, f5, hV⟩ =>
    ⟨hr4.trans (hr5.mono (by decide)), by rw [← hm4]; exact f5, ?_⟩
  rw [hV, V_eq4, V_eq4]
  rw [w2, c2] at e3
  have hv0 := hl s2
  rw [w2] at hv0
  exact unfold_twice hv0 (hl s3) (hl s4) hcy hv1 e3 e4

end

end VG.Proof.X25519.RISCV64.R64
