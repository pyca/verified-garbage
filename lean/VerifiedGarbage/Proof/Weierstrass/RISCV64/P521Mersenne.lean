module

-- separate module: its proofs (about 8 s) build in parallel with the code's literal, which its importer's
-- constant time evaluates
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Mersenne
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Field
import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Sqr
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
import VerifiedGarbage.Proof.X448.RISCV64.R64.Macc
import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Mul

/-!
# Montgomery's multiplication modulo P-521's prime by its Mersenne form, on RISC-V: the proofs

`mulCore` (`Impl/Weierstrass/RISCV64/P521Mersenne.lean`) meets GenWide's
specification of a multiplication (`GenWide.FastSpec`, and `GenWide.CoreSpec` for the copies' product) for `p = 2⁵²¹ - 1`
and `R = 2⁵⁷⁶` (`mulCore_spec`), so that GenWide's entry and copies make it
the function of the contract by register (`mul_rv`):

* the product's columns: each term's sums into the accumulator, with the
  next term's product and the one after's operands, which the pipeline
  (`Pipe`) carries from term to term (`step_ok`), the terms of a column
  (`terms_ok`) and the columns (`columns_ok`) by induction, which sum to the
  product (`mulCols_sum`, `productC_ok`);
* the square (`squareC_ok`): the cross products by the same pipeline (`tab_sq`), then
  each word doubled with the squares added (`dblStep_ok`, `dbls_ok`); twice the cross
  products plus the squares are the square (`sqCols_sum`);
* the folds, the correction and the rotation, word by word (`tail_ok`), after
  either (`mulCore_ok`, `sqCore_ok`), and the branch on the pointers (`core_spec`).
-/

@[expose] public section

-- `p`, below `2^576`, is evaluated.
set_option exponentiation.threshold 1200

namespace VG.Proof.Weierstrass.RISCV64.P521Mersenne

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P521Mersenne
open VG.Impl.Weierstrass.RISCV64.GenWide (T macStep adcCore)
open VG.Proof.Weierstrass.RISCV64.GenWide (clobS colsV_congr ctx_of mac_ok colsV_add' colsV_mul)
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.Weierstrass.RISCV64.P256Field (adc_ok)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-! ## The product -/

/-- The own working space GenWide's operations may write. -/
abbrev own (b : Addr) : Region := ⟨b + BitVec.ofNat 64 P, 160⟩

theorem P_eq : P = 1472 := rfl

/-- What the product needs. -/
structure PCtx (b A B : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  a : s.gpr .t4 = A
  bb : s.gpr .t5 = B
  aal : A.toNat % 8 = 0
  bal : B.toNat % 8 = 0
  ain : ∀ i < 9, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8
  bin : ∀ i < 9, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8
  adis : ∀ i < 9, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (own b)
  bdis : ∀ i < 9, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (own b)

/-- A part of the own working space within it. -/
theorem own_sub {b : Addr} {d n : Nat} (hd : P ≤ d) (hn : d + n ≤ P + 160) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (own b) :=
  Offset.sub b hd hn

/-- The `n` words of the product from word `i`. -/
abbrev pw (m : Mem) (b : Addr) (i n : Nat) : Nat := colsV (fun j => dw m b (P + 8 * i + 8 * j)) n

theorem colsV_split (f : Nat → Nat) (i : Nat) : ∀ n, colsV f (i + n) = colsV f i + (2 ^ 64) ^ i * colsV (fun j => f (i + j)) n
  | 0 => by simp [colsV]
  | n + 1 => by
    rw [← Nat.add_assoc, colsV, colsV_split f i n, colsV, Nat.pow_add, Nat.mul_add, Nat.mul_assoc]; omega

/-! ## The product by columns -/

section
open VG.Impl.X448.RISCV64.R64 (rr)
open VG.Proof.X448.RISCV64.R64 (tsum tsum_cons tsum_le)
open VG.Proof.Weierstrass.RISCV64.GenWide (clobW xv)

theorem rr_ne : ∀ k < 18, rr k ≠ rr (k + 1) ∧ rr k ≠ rr (k + 2) ∧ rr (k + 1) ≠ rr (k + 2) ∧ rr (k + 3) = rr k := by
  decide

theorem PR_cases (n : Nat) : PR n = (.a7, .t0) ∨ PR n = (.t3, .t6) := by
  unfold PR; split <;> simp

/-- Which registers the accumulator, the products and the operands use. -/
theorem rr_regs : ∀ k < 21, rr k ∈ clobW ∧ rr k ≠ .a1 ∧ rr k ≠ .a2 ∧ rr k ≠ .a7 ∧ rr k ≠ .t0 ∧ rr k ≠ .t3 ∧
    rr k ≠ .t6 := by decide

/-- A column's terms: `a_i b_j` for its pairs. -/
def mulF (X Y : Nat → Nat) (p : Nat × Nat) : Nat := X p.1 * Y p.2

def mulCs (X Y : Nat → Nat) (k : Nat) : Nat := tsum (mulF X Y) (colPairs k)

/-- The columns sum to the product. -/
theorem mulCols_sum (X Y : Nat → Nat) : colsV (mulCs X Y) 18 = colsV X 9 * colsV Y 9 := by
  simp only [colsV, mulCs, mulF, tsum, colPairs, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceSub, Nat.reduceLeDiff,
    Nat.reduceLT, and_self, and_true, and_false, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
  generalize 2 ^ 64 = W
  grind

theorem pstart_succ (cs : Nat → Nat) (k : Nat) : pstart cs (k + 1) = pstart cs k + cs k := by
  simp [pstart, List.range_succ]

/-- What the code of a table of terms `ts` needs: its terms are column `k`'s
pairs `ps k` in order, from `pstart` on, with words below 9. -/
structure Tab (ts : List (Nat × Nat × Nat)) (ps : Nat → List (Nat × Nat)) : Prop where
  take : ∀ k < 18, ∀ m < (ps k).length,
    (ps k).take (m + 1) = (ps k).take m ++ [(tm ts (pstart (fun c => (ps c).length) k + m)).2]
  le : ∀ k < 18, pstart (fun c => (ps c).length) k + (ps k).length ≤ ts.length
  lt : ∀ n < ts.length, (tm ts n).2.1 < 9 ∧ (tm ts n).2.2 < 9
  len : ∀ k < 18, (ps k).length ≤ 9

theorem tab_mul : Tab (terms colPairs) colPairs := ⟨by decide, by decide, by decide, by decide⟩

theorem tab_sq : Tab (terms sqPairs) sqPairs := ⟨by decide, by decide, by decide, by decide⟩

/-- What the terms keep, from the product's start `s0`. -/
structure TInv (b : Addr) (s0 s : State) : Prop where
  gpr : ∀ r, r ∉ clobW → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 P, 8 * 18⟩] s0.mem s.mem

theorem TInv.keeps {b : Addr} {s0 s s' : State} (h : TInv b s0 s) {rs : List Reg} (hk : Keeps rs s s')
    (hc : ∀ r ∈ rs, r ∈ clobW) : TInv b s0 s' :=
  ⟨fun r hr => (hk.1 r fun h => hr (hc r h)).trans (h.gpr r hr), hk.2.2.1.trans h.rd, hk.2.2.2.1.trans h.wr,
    hk.2.2.2.2.trans h.sp, by rw [hk.2.1]; exact h.frame⟩

theorem PR_clob (n : Nat) : ∀ r ∈ [(PR n).1, (PR n).2], r ∈ clobW := by
  rcases PR_cases n with h | h <;> rw [h] <;> decide

/-- A word of an operand, unchanged by the product's writes. -/
theorem op_eq {b A B : Addr} {s0 s : State} (h0 : PCtx b A B s0) (hI : TInv b s0 s) {i : Nat} (hi : i < 9) :
    dw s.mem A (8 * i) = dw s0.mem A (8 * i) ∧ dw s.mem B (8 * i) = dw s0.mem B (8 * i) := by
  have hP := P_eq
  exact ⟨dw_frame hI.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact GenWide.disj_sub (h0.adis i hi) (own_sub (by omega) (by omega)),
    dw_frame hI.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact GenWide.disj_sub (h0.bdis i hi) (own_sub (by omega) (by omega))⟩

/-- The pipeline at term `n`: its product in `PR n`, the next term's operands in `a1` and `a2`. -/
structure Pipe (X Y : Nat → Nat) (ts : List (Nat × Nat × Nat)) (n : Nat) (s : State) : Prop where
  prod : n < ts.length → (s.gpr (PR n).1).toNat + 2 ^ 64 * (s.gpr (PR n).2).toNat = X (tm ts n).2.1 * Y (tm ts n).2.2
  ops : n + 1 < ts.length → (s.gpr .a1).toNat = X (tm ts (n + 1)).2.1 ∧ (s.gpr .a2).toNat = Y (tm ts (n + 1)).2.2

theorem Pipe.of {X Y : Nat → Nat} {ts : List (Nat × Nat × Nat)} {n : Nat} {s s' : State} (h : Pipe X Y ts n s)
    (e1 : s'.gpr (PR n).1 = s.gpr (PR n).1) (e2 : s'.gpr (PR n).2 = s.gpr (PR n).2)
    (e3 : s'.gpr .a1 = s.gpr .a1) (e4 : s'.gpr .a2 = s.gpr .a2) : Pipe X Y ts n s' :=
  ⟨fun hn => by rw [e1, e2]; exact h.prod hn, fun hn => by rw [e3, e4]; exact h.ops hn⟩

/-- Term `n`'s product, if it is one. -/
theorem mulN_ok (ts : List (Nat × Nat × Nat)) (n : Nat) {s : State} :
    WP isa (.block (mulN ts n)) s fun s' =>
      (n < ts.length → (s'.gpr (PR n).1).toNat + 2 ^ 64 * (s'.gpr (PR n).2).toNat = (s.gpr .a1).toNat * (s.gpr .a2).toNat) ∧
        Keeps [(PR n).1, (PR n).2] s s' := by
  unfold mulN
  split
  · have hr : (PR n).1 ≠ .a1 ∧ (PR n).1 ≠ .a2 ∧ (PR n).1 ≠ (PR n).2 := by
      rcases PR_cases n with h | h <;> rw [h] <;> decide
    exact WP.mono (mulWide_ok hr.1 hr.2.1 hr.2.2) fun _ ⟨e, k⟩ => ⟨fun _ => e, k⟩
  · exact WP.block_nil ⟨fun h => absurd h ‹_›, Keeps.refl _ _⟩

/-- Term `n`'s operands, if it is one. -/
theorem ldN_ok {b A B : Addr} {s0 : State} (h0 : PCtx b A B s0) {ts : List (Nat × Nat × Nat)}
    (hlt : ∀ n < ts.length, (tm ts n).2.1 < 9 ∧ (tm ts n).2.2 < 9) (n : Nat) {s : State} (hI : TInv b s0 s) :
    WP isa (.block (ldN ts n)) s fun s' => Keeps [.a1, .a2] s s' ∧
      (n < ts.length → (s'.gpr .a1).toNat = dw s0.mem A (8 * (tm ts n).2.1) ∧
        (s'.gpr .a2).toNat = dw s0.mem B (8 * (tm ts n).2.2)) := by
  unfold ldN
  split
  · rename_i hn
    obtain ⟨hi, hj⟩ := hlt n hn
    have hA : s.gpr .t4 = A := (hI.gpr _ (by decide)).trans h0.a
    have hB : s.gpr .t5 = B := (hI.gpr _ (by decide)).trans h0.bb
    obtain ⟨eA, -⟩ := op_eq h0 hI hi
    obtain ⟨-, eB⟩ := op_eq h0 hI hj
    refine wp_ld (by omega) (by rw [hA]) (al8 h0.aal (by omega)) (by rw [hI.rd, hI.wr]; exact h0.ain _ hi)
      fun s1 u1 => ?_
    refine wp_ld (by omega) (by rw [u1.other _ (by decide), hB]) (al8 h0.bal (by omega))
      (by rw [u1.rd, u1.wr, hI.rd, hI.wr]; exact h0.bin _ hj) fun s2 u2 => WP.block_nil ?_
    refine ⟨⟨fun r hr => ?_, by rw [u2.mem, u1.mem], by rw [u2.rd, u1.rd], by rw [u2.wr, u1.wr],
      by rw [u2.sp, u1.sp]⟩, fun _ => ⟨?_, ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u2.other _ hr.2, u1.other _ hr.1]
    · rw [u2.other _ (by decide), u1.gpr, ← eA]; rfl
    · rw [u2.gpr, u1.mem, ← eB]; rfl
  · exact WP.block_nil ⟨Keeps.refl _ _, fun h => absurd h ‹_›⟩

set_option linter.unusedSimpArgs false in
/-- `l + 2⁶⁴ h + 2¹²⁸ t += p + 2⁶⁴ q`, for `q < 2⁶⁴ - 1`. -/
theorem accG_ok {l h t p q : Reg} (hlh : l ≠ h) (hlt : l ≠ t) (hht : h ≠ t)
    (hlp : l ≠ p) (hlq : l ≠ q) (hhp : h ≠ p) (hhq : h ≠ q) (htp : t ≠ p) (htq : t ≠ q) (hpq : p ≠ q) {s : State} :
    WP isa (.block [.add l l p, .sltu p l p, .add q q p, .add h h q, .sltu q h q, .add t t q]) s fun s' =>
      ((s.gpr q).toNat < 2 ^ 64 - 1 →
        val3 s' l h t = (val3 s l h t + ((s.gpr p).toNat + 2 ^ 64 * (s.gpr q).toNat)) % 2 ^ 192) ∧
      Keeps [l, h, t, p, q] s s' := by
  apply WP.of_runBlock
  simp only [val3, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, hlh, hlt, hht, hlp, hlq, hhp, hhq, htp, htq, hpq, Ne.symm hlh, Ne.symm hlt,
    Ne.symm hht, Ne.symm hlp, Ne.symm hlq, Ne.symm hhp, Ne.symm hhq, Ne.symm htp, Ne.symm htq, Ne.symm hpq,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have c₀ := Wide.carry (s.gpr l) (s.gpr p)
    have l₀ := Wide.carry_le (s.gpr l + s.gpr p < s.gpr p)
    generalize (if s.gpr l + s.gpr p < s.gpr p then (1 : BitVec 64) else 0) = k₀ at *
    have e₁ : (s.gpr q + k₀).toNat = (s.gpr q).toNat + k₀.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have c₁ := Wide.carry (s.gpr h) (s.gpr q + k₀)
    have l₁ := Wide.carry_le (s.gpr h + (s.gpr q + k₀) < s.gpr q + k₀)
    generalize (if s.gpr h + (s.gpr q + k₀) < s.gpr q + k₀ then (1 : BitVec 64) else 0) = k₁ at *
    rw [BitVec.toNat_add (s.gpr t)]
    rw [e₁] at c₁
    have := (s.gpr t).isLt
    have := (s.gpr l + s.gpr p).isLt
    have := (s.gpr h + (s.gpr q + k₀)).isLt
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem PR_mod (n : Nat) : PR (n % 2) = PR n := by
  simp only [PR, Nat.mod_mod]

theorem PR_mod1 (n : Nat) : PR (n % 2 + 1) = PR (n + 1) := by
  simp only [PR]; rw [show (n % 2 + 1) % 2 = (n + 1) % 2 by omega]

/-- The registers of a step's products, by the parity of the term. -/
theorem regs_pr : ∀ e < 2,
    (PR e).1 ≠ (PR e).2 ∧ (PR e).1 ≠ .a1 ∧ (PR e).1 ≠ .a2 ∧ (PR e).2 ≠ .a1 ∧ (PR e).2 ≠ .a2 ∧
    (PR e).1 ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧ (PR e).2 ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧
    (PR (e + 1)).1 ∉ [Reg.a1, .a2] ∧ (PR (e + 1)).2 ∉ [Reg.a1, .a2] := by decide

/-- The accumulator's register `r` apart from a step's others. -/
theorem regs_acc : ∀ k < 21, ∀ e < 2,
    rr k ≠ (PR e).1 ∧ rr k ≠ (PR e).2 ∧ rr k ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧ rr k ∉ [Reg.a1, .a2] := by
  decide

/-- The registers a step's sums write, apart from the next product's and the operands. -/
theorem regs_sum : ∀ k < 18, ∀ e < 2,
    (PR (e + 1)).1 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] ∧
    (PR (e + 1)).2 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] ∧
    Reg.a1 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] ∧
    Reg.a2 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] := by decide

/-- Term `n` of column `k`: the next product and operands, then this one's sums. -/
theorem pstep_ok {b A B : Addr} {s0 : State} (h0 : PCtx b A B s0) {ts : List (Nat × Nat × Nat)}
    (hlt : ∀ n < ts.length, (tm ts n).2.1 < 9 ∧ (tm ts n).2.2 < 9) {k n : Nat} (hk : k < 18) (hn : n < ts.length)
    {s : State} (hI : TInv b s0 s) (hp : Pipe (fun i => dw s0.mem A (8 * i)) (fun j => dw s0.mem B (8 * j)) ts n s)
    (hb : val3 s (rr k) (rr (k + 1)) (rr (k + 2)) +
      dw s0.mem A (8 * (tm ts n).2.1) * dw s0.mem B (8 * (tm ts n).2.2) < 2 ^ 192) :
    WP isa (.block (pstep ts k n)) s fun s' => TInv b s0 s' ∧ s'.mem = s.mem ∧
      Pipe (fun i => dw s0.mem A (8 * i)) (fun j => dw s0.mem B (8 * j)) ts (n + 1) s' ∧
      val3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) +
        dw s0.mem A (8 * (tm ts n).2.1) * dw s0.mem B (8 * (tm ts n).2.2) := by
  obtain ⟨h01, h02, h12, -⟩ := rr_ne k hk
  obtain ⟨c0, r01, r02, r07, r00, r03, r06⟩ := rr_regs k (by omega)
  obtain ⟨c1, r11, r12, r17, r10, r13, r16⟩ := rr_regs (k + 1) (by omega)
  obtain ⟨c2, r21, r22, r27, r20, r23, r26⟩ := rr_regs (k + 2) (by omega)
  -- The registers, by the parity of `n`.
  have he : n % 2 < 2 := Nat.mod_lt _ (by decide)
  have h1 := regs_pr _ he
  have h2 := regs_acc k (by omega) _ he
  have h3 := regs_acc (k + 1) (by omega) _ he
  have h4 := regs_acc (k + 2) (by omega) _ he
  have h5 := regs_sum k hk _ he
  rw [PR_mod, PR_mod1] at h1 h2 h3 h4 h5
  obtain ⟨p12, p1a1, p1a2, p2a1, p2a2, p1n, p2n, q1a, q2a⟩ := h1
  obtain ⟨a1p, a2p, z0n, z0a⟩ := h2
  obtain ⟨b1p, b2p, z1n, z1a⟩ := h3
  obtain ⟨c1p, c2p, z2n, z2a⟩ := h4
  obtain ⟨q1n, q2n, a1n, a2n⟩ := h5
  unfold pstep
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (mulN_ok ts (n + 1)) fun s1 ⟨e1, k1⟩ => ?_)
  have hI1 := hI.keeps k1 (PR_clob _)
  refine WP.block_append (WP.mono (ldN_ok h0 hlt (n + 2) hI1) fun s2 ⟨k2, e2⟩ => ?_)
  have hI2 := hI1.keeps k2 (by decide)
  have g1 : ∀ r, r ∉ [(PR (n + 1)).1, (PR (n + 1)).2] → r ∉ [Reg.a1, .a2] → s2.gpr r = s.gpr r :=
    fun r h1 h2 => (k2.1 r h2).trans (k1.1 r h1)
  have pp := hp.prod hn
  rw [← g1 _ p1n (by simp [p1a1, p1a2]), ← g1 _ p2n (by simp [p2a1, p2a2])] at pp
  have hv2 : val3 s2 (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) := by
    simp only [val3]
    rw [g1 _ z0n z0a, g1 _ z1n z1a, g1 _ z2n z2a]
  have hX := dw_lt s0.mem A (8 * (tm ts n).2.1)
  have hY := dw_lt s0.mem B (8 * (tm ts n).2.2)
  have hXY : dw s0.mem A (8 * (tm ts n).2.1) * dw s0.mem B (8 * (tm ts n).2.2) ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hq : (s2.gpr (PR n).2).toNat < 2 ^ 64 - 1 := by
    have := (s2.gpr (PR n).1).isLt
    omega
  refine WP.mono (accG_ok h01 h02 h12 a1p a2p b1p b2p c1p c2p p12) fun s3 ⟨e3, k3⟩ => ?_
  have hI3 := hI2.keeps k3 (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact c0
    · exact c1
    · exact c2
    · exact PR_clob n _ (by simp)
    · exact PR_clob n _ (by simp))
  refine ⟨hI3, by rw [k3.2.1, k2.2.1, k1.2.1], ⟨fun hn1 => ?_, fun hn2 => ?_⟩, ?_⟩
  · rw [k3.1 _ q1n, k3.1 _ q2n, k2.1 _ q1a, k2.1 _ q2a, (e1 hn1)]
    obtain ⟨o1, o2⟩ := hp.ops hn1
    rw [o1, o2]
  · rw [k3.1 _ a1n, k3.1 _ a2n]
    exact e2 hn2
  · rw [e3 hq, hv2, pp, Nat.mod_eq_of_lt hb]

theorem tsum_mul_lt {X Y : Nat → Nat} (hX : ∀ i, X i < 2 ^ 64) (hY : ∀ j, Y j < 2 ^ 64)
    {ps : List (Nat × Nat)} (hl : ps.length ≤ 9) : tsum (mulF X Y) ps < 9 * 2 ^ 128 := by
  have hle : ∀ p ∈ ps, mulF X Y p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := fun p _ =>
    Nat.mul_le_mul (by have := hX p.1; omega) (by have := hY p.2; omega)
  have := tsum_le hle
  have : ps.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) ≤ 9 * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) :=
    Nat.mul_le_mul_right _ hl
  omega

theorem tsum_snoc (f : Nat × Nat → Nat) (ps : List (Nat × Nat)) (p : Nat × Nat) :
    tsum f (ps ++ [p]) = tsum f ps + f p := by simp [tsum]

/-- Column `k`'s first `m` terms, by induction on them. -/
theorem pterms_ok {b A B : Addr} {s0 : State} (h0 : PCtx b A B s0) {ts : List (Nat × Nat × Nat)}
    {ps : Nat → List (Nat × Nat)} (ht : Tab ts ps) {k : Nat} (hk : k < 18) :
    ∀ m ≤ (ps k).length, ∀ s, TInv b s0 s →
      Pipe (fun i => dw s0.mem A (8 * i)) (fun j => dw s0.mem B (8 * j)) ts (pstart (fun c => (ps c).length) k) s →
      val3 s (rr k) (rr (k + 1)) (rr (k + 2)) < 2 ^ 128 →
      WP isa (.block ((List.range' (pstart (fun c => (ps c).length) k) m).flatMap (pstep ts k))) s fun s' => TInv b s0 s' ∧ s'.mem = s.mem ∧
        Pipe (fun i => dw s0.mem A (8 * i)) (fun j => dw s0.mem B (8 * j)) ts (pstart (fun c => (ps c).length) k + m) s' ∧
        val3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) +
          tsum (mulF (fun i => dw s0.mem A (8 * i)) (fun j => dw s0.mem B (8 * j))) ((ps k).take m)
  | 0, _, s, hI, hp, _ => WP.block_nil ⟨hI, rfl, hp, by simp [tsum]⟩
  | m + 1, hm, s, hI, hp, hv => by
    rw [List.range'_concat, Nat.one_mul, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (pterms_ok h0 ht hk m (by omega) s hI hp hv) fun s1 ⟨hI1, m1, hp1, hv1⟩ => ?_)
    have hX : ∀ i, dw s0.mem A (8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
    have hY : ∀ j, dw s0.mem B (8 * j) < 2 ^ 64 := fun j => dw_lt _ _ _
    have hts := tsum_mul_lt hX hY (ps := (ps k).take m)
      (by rw [List.length_take]; exact Nat.le_trans (Nat.min_le_right _ _) (ht.len k hk))
    have hxy : dw s0.mem A (8 * (tm ts (pstart (fun c => (ps c).length) k + m)).2.1) * dw s0.mem B (8 * (tm ts (pstart (fun c => (ps c).length) k + m)).2.2) <
        2 ^ 128 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (hX _) (hY _)) (by decide)
    refine WP.mono (pstep_ok h0 ht.lt hk (by have := ht.le k hk; omega) hI1 hp1 (by rw [hv1]; omega))
      fun s2 ⟨hI2, m2, hp2, hv2⟩ => ⟨hI2, m2.trans m1, by rw [← Nat.add_assoc]; exact hp2, ?_⟩
    rw [hv2, hv1, ht.take k hk m (by omega), tsum_snoc]
    simp only [mulF]; omega

/-- After `k` columns: the words below `T + 8k` and the accumulator hold the
first `k` columns' sum, and the pipeline is at column `k`'s first term. -/
structure CInv (b A B : Addr) (s0 : State) (ts : List (Nat × Nat × Nat)) (ps : Nat → List (Nat × Nat)) (k : Nat) (s : State) : Prop where
  t : TInv b s0 s
  pipe : Pipe (fun i => dw s0.mem A (8 * i)) (fun j => dw s0.mem B (8 * j)) ts (pstart (fun c => (ps c).length) k) s
  top : s.gpr (rr (k + 2)) = 0
  val : colsV (fun c => dw s.mem b (P + 8 * c)) k + (2 ^ 64) ^ k * ((s.gpr (rr k)).toNat + 2 ^ 64 * (s.gpr (rr (k + 1))).toNat) =
    colsV (fun c => tsum (mulF (fun i => dw s0.mem A (8 * i)) (fun j => dw s0.mem B (8 * j))) (ps c)) k

/-- Column `k`: its terms, then its low word stored and its register zeroed. -/
theorem pcol_ok {b A B : Addr} {s0 : State} (h0 : PCtx b A B s0) {ts : List (Nat × Nat × Nat)}
    {ps : Nat → List (Nat × Nat)} (ht : Tab ts ps) {k : Nat} (hk : k < 18) {s : State}
    (h : CInv b A B s0 ts ps k s) :
    WP isa (.block (pcol ts (fun c => (ps c).length) k)) s
      (CInv b A B s0 ts ps (k + 1)) := by
  have hP := P_eq
  have hb := h0.nowrap
  obtain ⟨h01, h02, h12, h3⟩ := rr_ne k hk
  obtain ⟨c0, -⟩ := rr_regs k (by omega)
  obtain ⟨x1, x2, -, z0a⟩ := regs_acc k (by omega) _ (Nat.mod_lt (pstart (fun c => (ps c).length) (k + 1)) (by decide))
  rw [PR_mod] at x1 x2
  have hv0 : val3 s (rr k) (rr (k + 1)) (rr (k + 2)) =
      (s.gpr (rr k)).toNat + 2 ^ 64 * (s.gpr (rr (k + 1))).toNat := by
    simp only [val3, h.top]; rfl
  have hl := (s.gpr (rr k)).isLt
  have hh := (s.gpr (rr (k + 1))).isLt
  unfold pcol
  refine WP.block_append (WP.mono (pterms_ok h0 ht hk _ (Nat.le_refl _) s h.t h.pipe (by rw [hv0]; omega_arith))
    fun s1 ⟨hI1, m1, hp1, hv1⟩ => ?_)
  rw [List.take_length] at hv1
  rw [← pstart_succ] at hp1
  have hc1 : Ctx b s1 := ctx_of h0.ctx (hI1.gpr _ (by decide)) hI1.wr
  refine sd_ok hc1 (by omega) (by omega) fun s2 u2 => wp_li (by decide) fun s3 u3 => WP.block_nil ?_
  have hm : s3.mem = s1.mem.writeW (b + BitVec.ofNat 64 (P + 8 * k)) (s1.gpr (rr k)) := by
    rw [u3.mem, u2.mem]
  have g3 : ∀ r, r ≠ rr k → s3.gpr r = s1.gpr r := fun r hr => by rw [u3.other r hr, u2.gpr]
  refine ⟨⟨fun r hr => (g3 r (fun e => hr (e ▸ c0))).trans (hI1.gpr r hr), by rw [u3.rd, u2.rd, hI1.rd],
      by rw [u3.wr, u2.wr, hI1.wr], by rw [u3.sp, u2.sp, hI1.sp], ?_⟩,
      hp1.of (g3 _ (Ne.symm x1)) (g3 _ (Ne.symm x2)) (g3 _ fun e => z0a (by rw [← e]; simp))
        (g3 _ fun e => z0a (by rw [← e]; simp)), ?_, ?_⟩
  · rw [hm]
    exact hI1.frame.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))
  · rw [show k + 1 + 2 = k + 3 by omega, h3, u3.gpr]; rfl
  · have e1 : s3.gpr (rr (k + 1)) = s1.gpr (rr (k + 1)) := g3 _ (Ne.symm h01)
    have e2 : s3.gpr (rr (k + 1 + 1)) = s1.gpr (rr (k + 2)) := by
      rw [show k + 1 + 1 = k + 2 by omega]; exact g3 _ (Ne.symm h02)
    have ea : colsV (fun c => dw s3.mem b (P + 8 * c)) k = colsV (fun c => dw s.mem b (P + 8 * c)) k :=
      colsV_congr fun c hc' => by rw [hm, dw_write_other _ _ _ (by omega) (by omega) (by omega), m1]
    have ek : dw s3.mem b (P + 8 * k) = (s1.gpr (rr k)).toNat := by rw [hm, dw_write_self]
    have hval := h.val
    rw [colsV, ea, ek, e1, e2]
    rw [colsV, ← hval]
    have hv1' : val3 s1 (rr k) (rr (k + 1)) (rr (k + 2)) = (s.gpr (rr k)).toNat + 2 ^ 64 * (s.gpr (rr (k + 1))).toNat +
        tsum (mulF (fun i => dw s0.mem A (8 * i)) (fun j => dw s0.mem B (8 * j))) (ps k) := by rw [hv1, hv0]
    simp only [val3] at hv1'
    rw [Nat.pow_succ (n := 2 ^ 64)]
    generalize (2 ^ 64) ^ k = K at *
    generalize (s1.gpr (rr k)).toNat = a at *
    generalize (s1.gpr (rr (k + 1))).toNat = c at *
    generalize (s1.gpr (rr (k + 2))).toNat = d at *
    generalize tsum (mulF (fun i => dw s0.mem A (8 * i)) (fun j => dw s0.mem B (8 * j))) (ps k) = t at *
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by decide] at hv1'
    generalize 2 ^ 64 = W at *
    grind

/-- The columns, by induction. -/
theorem columns_ok {b A B : Addr} {s0 : State} (h0 : PCtx b A B s0) {ts : List (Nat × Nat × Nat)}
    {ps : Nat → List (Nat × Nat)} (ht : Tab ts ps) :
    ∀ n ≤ 18, ∀ s, CInv b A B s0 ts ps 0 s →
      WP isa (.block ((List.range n).flatMap (pcol ts (fun c => (ps c).length)))) s
        (CInv b A B s0 ts ps n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (columns_ok h0 ht n (by omega) s h) fun s1 h1 => pcol_ok h0 ht (by omega) h1)

/-- The product's eighteen words. -/
structure ProdOk (b A B : Addr) (s0 s : State) : Prop where
  gpr : ∀ r, r ∉ clobW → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 P, 8 * 18⟩] s0.mem s.mem
  val : pw s.mem b 0 18 = xv s0.mem A 9 * xv s0.mem B 9

/-- `pipe ts`: the columns of the terms `ts` at `T`. -/
theorem pipe_ok {b A B : Addr} {s0 : State} (h0 : PCtx b A B s0) {ts : List (Nat × Nat × Nat)}
    {ps : Nat → List (Nat × Nat)} (ht : Tab ts ps) :
    WP isa (.block (pipe ts (fun c => (ps c).length))) s0 (CInv b A B s0 ts ps 18) := by
  unfold pipe
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => wp_li (by decide) fun s3 u3 => ?_
  have hI3 : TInv b s0 s3 :=
    (TInv.keeps (s := s0) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩ (rs := [.a4, .a5, .a6])
      ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u3.other _ hr.2.2, u2.other _ hr.2.1, u1.other _ hr.1],
       by rw [u3.mem, u2.mem, u1.mem], by rw [u3.rd, u2.rd, u1.rd], by rw [u3.wr, u2.wr, u1.wr],
       by rw [u3.sp, u2.sp, u1.sp]⟩ (by decide))
  refine WP.block_append (WP.mono (ldN_ok h0 ht.lt 0 hI3) fun s4 ⟨k4, e4⟩ => ?_)
  have hI4 := hI3.keeps k4 (by decide)
  refine WP.block_append (WP.mono (mulN_ok ts 0) fun s5 ⟨e5, k5⟩ => ?_)
  have hI5 := hI4.keeps k5 (PR_clob 0)
  refine WP.block_append (WP.mono (ldN_ok h0 ht.lt 1 hI5) fun s6 ⟨k6, e6⟩ => ?_)
  have hI6 := hI5.keeps k6 (by decide)
  have hacc : ∀ r ∈ [Reg.a4, .a5, .a6], s6.gpr r = s3.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [k6.1 _ (by rcases hr with rfl | rfl | rfl <;> decide), k5.1 _ (by rcases hr with rfl | rfl | rfl <;> decide),
      k4.1 _ (by rcases hr with rfl | rfl | rfl <;> decide)]
  have hC0 : CInv b A B s0 ts ps 0 s6 := ⟨hI6, ⟨fun hn => ?_, fun hn => ?_⟩, ?_, ?_⟩
  · exact columns_ok h0 ht 18 (Nat.le_refl _) s6 hC0
  · -- The first product.
    rw [show pstart (fun c => (ps c).length) 0 = 0 from rfl] at hn ⊢
    have e5' := e5 hn
    rw [show PR 0 = (Reg.a7, Reg.t0) from rfl] at e5' ⊢
    rw [k6.1 .a7 (by decide), k6.1 .t0 (by decide), e5']
    obtain ⟨o1, o2⟩ := e4 hn
    rw [o1, o2]
  · -- The second's operands.
    rw [show pstart (fun c => (ps c).length) 0 = 0 from rfl] at hn ⊢
    exact e6 hn
  · rw [show rr (0 + 2) = .a6 from rfl, hacc _ (by simp), u3.gpr]; rfl
  · simp only [colsV, show rr 0 = .a4 from rfl, show rr (0 + 1) = .a5 from rfl, hacc .a4 (by simp),
      hacc .a5 (by simp), u3.other .a4 (by decide), u3.other .a5 (by decide), u2.gpr, u2.other .a4 (by decide), u1.gpr]
    rfl

/-- After the eighteen columns, `T` holds their sum, if it fits. -/
theorem CInv.final {b A B : Addr} {s0 : State} {ts : List (Nat × Nat × Nat)} {ps : Nat → List (Nat × Nat)}
    {s : State} (h : CInv b A B s0 ts ps 18 s) {V : Nat}
    (hV : colsV (fun c => tsum (mulF (fun i => dw s0.mem A (8 * i)) (fun j => dw s0.mem B (8 * j))) (ps c)) 18 = V)
    (hlt : V < (2 ^ 64) ^ 18) : pw s.mem b 0 18 = V := by
  have hv := h.val
  rw [hV] at hv
  have hT := GenWide.colsV_lt (fun c => dw s.mem b (P + 8 * c)) (fun _ => dw_lt _ _ _) 18
  show colsV (fun j => dw s.mem b (P + 8 * 0 + 8 * j)) 18 = _
  simp only [Nat.mul_zero, Nat.add_zero]
  generalize (2 ^ 64) ^ 18 = K at *
  generalize colsV (fun c => dw s.mem b (P + 8 * c)) 18 = X at *
  generalize (s.gpr (rr 18)).toNat + 2 ^ 64 * (s.gpr (rr (18 + 1))).toNat = C at *
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · omega
  · have : K ≤ K * C := Nat.le_mul_of_pos_right _ hC
    omega

/-- `productC`: `T = [t4] [t5]`. -/
theorem productC_ok {b A B : Addr} {s0 : State} (h0 : PCtx b A B s0) :
    WP isa (.block productC) s0 (ProdOk b A B s0) := by
  refine WP.mono (pipe_ok h0 tab_mul) fun s' h' => ⟨h'.t.gpr, h'.t.rd, h'.t.wr, h'.t.sp, h'.t.frame, ?_⟩
  have hlt : xv s0.mem A 9 * xv s0.mem B 9 < (2 ^ 64) ^ 18 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (GenWide.colsV_lt _ (fun _ => dw_lt _ _ _) 9)
      (GenWide.colsV_lt _ (fun _ => dw_lt _ _ _) 9)) (by rw [← Nat.pow_add])
  exact h'.final (mulCols_sum _ _) hlt

/-! ### The square -/

/-- A cross term's value: `a_j a_i` for the term `(i, j)`. -/
def sqF (X : Nat → Nat) (p : Nat × Nat) : Nat := X p.2 * X p.1

/-- The columns of the cross products. -/
def sqCs (X : Nat → Nat) (k : Nat) : Nat := tsum (sqF X) (sqPairs k)

theorem sqCs_eq (X : Nat → Nat) : sqCs X = fun k => tsum (mulF X X) (sqPairs k) := by
  funext k; unfold sqCs tsum; congr 1; exact List.map_congr_left fun p _ => Nat.mul_comm _ _

/-- The squares `a_i²` at `2¹²⁸ⁱ`. -/
def dsq (X : Nat → Nat) : Nat :=
  X 0 * X 0 + (2 ^ 64) ^ 2 * (X 1 * X 1) + (2 ^ 64) ^ 4 * (X 2 * X 2) + (2 ^ 64) ^ 6 * (X 3 * X 3) +
    (2 ^ 64) ^ 8 * (X 4 * X 4) + (2 ^ 64) ^ 10 * (X 5 * X 5) + (2 ^ 64) ^ 12 * (X 6 * X 6) +
    (2 ^ 64) ^ 14 * (X 7 * X 7) + (2 ^ 64) ^ 16 * (X 8 * X 8)

/-- Twice the cross products' columns, plus the squares, are the square. -/
theorem sqCols_sum (X : Nat → Nat) : 2 * colsV (sqCs X) 18 + dsq X = colsV X 9 * colsV X 9 := by
  simp only [colsV, dsq, sqCs, sqPairs, colPairs, tsum, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil,
    List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sqF, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  generalize 2 ^ 64 = B
  grind

open VG.Proof.X448.RISCV64.R64 (dq dbw cp dq_lt dbw_lt colsV_dbw colsV_add dbl1_ok dbl2_ok dbl3e_ok dbl3o_ok
  dbl4_ok) in
/-- The words of the squares are the squares. -/
theorem colsV_dq (X : Nat → Nat) : colsV (dq X) 18 = dsq X := by
  simp only [colsV, dq, dsq]
  simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]
  have h0 := Nat.mod_add_div (X 0 * X 0) (2 ^ 64)
  have h1 := Nat.mod_add_div (X 1 * X 1) (2 ^ 64)
  have h2 := Nat.mod_add_div (X 2 * X 2) (2 ^ 64)
  have h3 := Nat.mod_add_div (X 3 * X 3) (2 ^ 64)
  have h4 := Nat.mod_add_div (X 4 * X 4) (2 ^ 64)
  have h5 := Nat.mod_add_div (X 5 * X 5) (2 ^ 64)
  have h6 := Nat.mod_add_div (X 6 * X 6) (2 ^ 64)
  have h7 := Nat.mod_add_div (X 7 * X 7) (2 ^ 64)
  have h8 := Nat.mod_add_div (X 8 * X 8) (2 ^ 64)
  generalize X 0 * X 0 % 2 ^ 64 = l0 at *
  generalize X 1 * X 1 % 2 ^ 64 = l1 at *
  generalize X 2 * X 2 % 2 ^ 64 = l2 at *
  generalize X 3 * X 3 % 2 ^ 64 = l3 at *
  generalize X 4 * X 4 % 2 ^ 64 = l4 at *
  generalize X 5 * X 5 % 2 ^ 64 = l5 at *
  generalize X 6 * X 6 % 2 ^ 64 = l6 at *
  generalize X 7 * X 7 % 2 ^ 64 = l7 at *
  generalize X 8 * X 8 % 2 ^ 64 = l8 at *
  generalize X 0 * X 0 / 2 ^ 64 = u0 at *
  generalize X 1 * X 1 / 2 ^ 64 = u1 at *
  generalize X 2 * X 2 / 2 ^ 64 = u2 at *
  generalize X 3 * X 3 / 2 ^ 64 = u3 at *
  generalize X 4 * X 4 / 2 ^ 64 = u4 at *
  generalize X 5 * X 5 / 2 ^ 64 = u5 at *
  generalize X 6 * X 6 / 2 ^ 64 = u6 at *
  generalize X 7 * X 7 / 2 ^ 64 = u7 at *
  generalize X 8 * X 8 / 2 ^ 64 = u8 at *
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, ← h8]
  generalize 2 ^ 64 = B
  grind

section
open VG.Proof.X448.RISCV64.R64 (dq dbw cp dq_lt dbw_lt colsV_dbw colsV_add dbl1_ok dbl2_ok dbl3e_ok dbl3o_ok
  dbl4_ok)

/-- Before step `k` of the doubling, from `s0` (the start of the square):
the words of `X` from `k` on unchanged (`C`), `X`'s word `k - 1` in `a5`, the
high word of the last square in `t3` (for odd `k`), the carry in `a4`, and
the words below `k` with the carry the first `k` words of the square. -/
structure DblInv (b A : Addr) (s0 : State) (C : Nat → Nat) (k : Nat) (s : State) : Prop where
  t : TInv b s0 s
  hi : ∀ i, k ≤ i → i < 18 → dw s.mem b (P + 8 * i) = C i
  prev : (s.gpr .a5).toNat = if k = 0 then 0 else C (k - 1)
  sqhi : k % 2 = 1 → (s.gpr .t3).toNat = dw s0.mem A (8 * (k / 2)) * dw s0.mem A (8 * (k / 2)) / 2 ^ 64
  cy : (s.gpr .a4).toNat ≤ 2
  val : colsV (fun c => dw s.mem b (P + 8 * c)) k + (2 ^ 64) ^ k * (s.gpr .a4).toNat =
    colsV (fun c => dbw C c + dq (fun i => dw s0.mem A (8 * i)) c) k

/-- The end of step `k`: the carry added, the word stored. -/
theorem dblEnd_ok {b A B : Addr} {s0 : State} (h0 : PCtx b A B s0) {C : Nat → Nat}
    (hC : ∀ i, C i < 2 ^ 64) {k : Nat} (hk : k < 18) {s s4 : State}
    (h : DblInv b A s0 C k s) (hI4 : TInv b s0 s4) (hm4 : s4.mem = s.mem)
    (h4 : s4.gpr .a4 = s.gpr .a4) (h5 : (s4.gpr .a5).toNat = C k)
    (hv : (s4.gpr .a6).toNat + 2 ^ 64 * (s4.gpr .a7).toNat = dbw C k + dq (fun i => dw s0.mem A (8 * i)) k)
    (ht : (k + 1) % 2 = 1 → (s4.gpr .t3).toNat =
      dw s0.mem A (8 * ((k + 1) / 2)) * dw s0.mem A (8 * ((k + 1) / 2)) / 2 ^ 64) :
    WP isa (.block (([.add .a6 .a6 .a4, .sltu .t0 .a6 .a4, .add .a4 .a7 .t0] : List Instr) ++
      ([.store .d .a6 .a3 (P + 8 * k)] : List Instr))) s4 (DblInv b A s0 C (k + 1)) := by
  have hP := P_eq
  have hb := h0.nowrap
  have hb1 := dbw_lt hC k
  have hb2 := dq_lt (X := fun i => dw s0.mem A (8 * i)) (fun i => dw_lt _ _ _) k
  have h7 : (s4.gpr .a7).toNat ≤ 1 := by
    have := (s4.gpr .a6).isLt
    omega
  refine WP.block_append (WP.mono dbl4_ok fun s5 ⟨e5, k5⟩ => ?_)
  have hI5 := hI4.keeps k5 (by decide)
  have hc5 : Ctx b s5 := ctx_of h0.ctx (hI5.gpr _ (by decide)) hI5.wr
  refine sd_ok hc5 (by omega) (by omega) fun s6 u6 => WP.block_nil ?_
  have hm6 : s6.mem = s.mem.writeW (b + BitVec.ofNat 64 (P + 8 * k)) (s5.gpr .a6) := by
    rw [u6.mem, k5.2.1, hm4]
  have e5' := e5 h7
  rw [h4] at e5'
  have hcy := h.cy
  have hv6 : (s6.gpr .a6).toNat + 2 ^ 64 * (s6.gpr .a4).toNat =
      dbw C k + dq (fun i => dw s0.mem A (8 * i)) k + (s.gpr .a4).toNat := by
    rw [u6.gpr]; omega
  refine ⟨⟨fun r hr => by rw [u6.gpr]; exact hI5.gpr r hr, by rw [u6.rd, hI5.rd], by rw [u6.wr, hI5.wr],
    by rw [u6.sp, hI5.sp], ?_⟩, fun i hi hi' => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm6]
    exact h.t.frame.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))
  · rw [hm6, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    exact h.hi i (by omega) hi'
  · rw [u6.gpr, k5.1 _ (by decide), h5]; simp
  · intro hk1; rw [u6.gpr, k5.1 _ (by decide)]; exact ht hk1
  · have := (s6.gpr .a6).isLt
    omega
  · have ea : colsV (fun c => dw s6.mem b (P + 8 * c)) k = colsV (fun c => dw s.mem b (P + 8 * c)) k :=
      colsV_congr fun c hc' => by rw [hm6, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have ek : dw s6.mem b (P + 8 * k) = (s5.gpr .a6).toNat := by rw [hm6, dw_write_self]
    rw [colsV, ea, ek, colsV, ← h.val, Nat.pow_succ (n := 2 ^ 64)]
    rw [u6.gpr] at hv6 ⊢
    generalize (2 ^ 64) ^ k = K at *
    generalize (s5.gpr .a6).toNat = a at *
    generalize (s5.gpr .a4).toNat = c at *
    generalize (s.gpr .a4).toNat = d at *
    generalize dbw C k + dq (fun i => dw s0.mem A (8 * i)) k = t at *
    generalize 2 ^ 64 = W at *
    grind

theorem dblStep_ok {b A B : Addr} {s0 : State} (h0 : PCtx b A B s0) {C : Nat → Nat}
    (hC : ∀ i, C i < 2 ^ 64) {k : Nat} (hk : k < 18) {s : State} (h : DblInv b A s0 C k s) :
    WP isa (.block (dblStep k)) s (DblInv b A s0 C (k + 1)) := by
  have hP := P_eq
  have hb := h0.nowrap
  have e : dblStep k = [.shift .srl .d .a7 .a5 63] ++ (.load .d .a5 .a3 (P + 8 * k) ::
      ([.shift .sll .d .a6 .a5 1, .logic .or .a6 .a6 .a7] ++
        ((if k % 2 = 0 then
          .load .d .t3 .t4 (8 * (k / 2)) :: [.mul .t0 .t3 .t3, .mulhu .t3 .t3 .t3,
            .add .a6 .a6 .t0, .sltu .a7 .a6 .t0]
         else [.add .a6 .a6 .t3, .sltu .a7 .a6 .t3]) ++
        ([.add .a6 .a6 .a4, .sltu .t0 .a6 .a4, .add .a4 .a7 .t0] ++
          [.store .d .a6 .a3 (P + 8 * k)])))) := by
    simp only [dblStep, List.cons_append, List.nil_append]
  rw [e]
  refine WP.block_append (WP.mono dbl1_ok fun s1 ⟨e1, k1⟩ => ?_)
  have hI1 := h.t.keeps k1 (by decide)
  have hc1 : Ctx b s1 := ctx_of h0.ctx (hI1.gpr _ (by decide)) hI1.wr
  refine ld_ok hc1 (by omega) (by omega) fun s2 u2 => ?_
  have hI2 := hI1.keeps (rs := [.a5]) ⟨fun r hr => u2.other r (by simpa using hr), u2.mem, u2.rd, u2.wr, u2.sp⟩
    (by decide)
  refine WP.block_append (WP.mono dbl2_ok fun s3 ⟨e3, k3⟩ => ?_)
  have hck : (s2.gpr .a5).toNat = C k := by
    rw [u2.gpr, show (s1.mem.readW _ 64).toNat = dw s1.mem b (P + 8 * k) from rfl, k1.2.1]
    exact h.hi k (Nat.le_refl _) hk
  have hp7 : (s2.gpr .a7).toNat = cp C k := by
    rw [u2.other _ (by decide), e1, h.prev, cp]
    split <;> simp
  have hp1 : (s2.gpr .a7).toNat ≤ 1 := by
    have := (s.gpr .a5).isLt
    rw [u2.other _ (by decide), e1]; omega
  have ha6 : (s3.gpr .a6).toNat = dbw C k := by rw [e3 hp1, hck, hp7]; rfl
  have hm3 : s3.mem = s.mem := by rw [k3.2.1, u2.mem, k1.2.1]
  have hI3 := hI2.keeps k3 (by decide)
  have h4s : s3.gpr .a4 = s.gpr .a4 := by
    rw [k3.1 _ (by decide), u2.other _ (by decide), k1.1 _ (by decide)]
  have h5s : (s3.gpr .a5).toNat = C k := by rw [k3.1 _ (by decide)]; exact hck
  by_cases hpar : k % 2 = 0
  · rw [ite_eq_left hpar, List.cons_append]
    have hi : k / 2 < 9 := by omega
    have hA3 : s3.gpr .t4 = A := (hI3.gpr _ (by decide)).trans h0.a
    refine wp_ld (by omega) (by rw [hA3]) (al8 h0.aal (by omega)) (by rw [hI3.rd, hI3.wr]; exact h0.ain _ hi)
      fun s4 u4 => ?_
    have hI4 := hI3.keeps (rs := [.t3]) ⟨fun r hr => u4.other r (by simpa using hr), u4.mem, u4.rd, u4.wr, u4.sp⟩
      (by decide)
    refine WP.block_append (WP.mono dbl3e_ok fun s5 ⟨e5, f5, k5⟩ => ?_)
    have ht4 : (s4.gpr .t3).toNat = dw s0.mem A (8 * (k / 2)) := by
      rw [u4.gpr, ← (op_eq h0 hI3 hi).1]; rfl
    refine dblEnd_ok h0 hC hk h (hI4.keeps k5 (by decide))
      (by rw [k5.2.1, u4.mem, hm3]) (by rw [k5.1 _ (by decide), u4.other _ (by decide), h4s])
      (by rw [k5.1 _ (by decide), u4.other _ (by decide), h5s]) ?_ ?_
    · rw [e5, u4.other _ (by decide), ha6, ht4, dq, ite_eq_left hpar]
    · intro _
      rw [f5, ht4, show (k + 1) / 2 = k / 2 by omega]
  · rw [ite_eq_right hpar]
    refine WP.block_append (WP.mono dbl3o_ok fun s5 ⟨e5, k5⟩ => ?_)
    have ht3 : (s3.gpr .t3).toNat = dw s0.mem A (8 * (k / 2)) * dw s0.mem A (8 * (k / 2)) / 2 ^ 64 := by
      rw [k3.1 _ (by decide), u2.other _ (by decide), k1.1 _ (by decide)]
      exact h.sqhi (by omega)
    refine dblEnd_ok h0 hC hk h (hI3.keeps k5 (by decide))
      (by rw [k5.2.1, hm3]) (by rw [k5.1 _ (by decide), h4s])
      (by rw [k5.1 _ (by decide), h5s]) ?_ (fun h' => absurd h' (by omega))
    rw [e5, ha6, ht3, dq, ite_eq_right hpar]

/-- The steps of the doubling, by induction. -/
theorem dbls_ok {b A B : Addr} {s0 : State} (h0 : PCtx b A B s0) {C : Nat → Nat} (hC : ∀ i, C i < 2 ^ 64) :
    ∀ n ≤ 18, ∀ s, DblInv b A s0 C 0 s →
      WP isa (.block ((List.range n).flatMap dblStep)) s (DblInv b A s0 C n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (dbls_ok h0 hC n (by omega) s h) fun s1 h1 => dblStep_ok h0 hC (by omega) h1)

/-- `squareC`: `T = [t4]²`, for equal operands. -/
theorem squareC_ok {b A : Addr} {s0 : State} (h0 : PCtx b A A s0) :
    WP isa (.block squareC) s0 (ProdOk b A A s0) := by
  have hP := P_eq
  have hX : ∀ i, dw s0.mem A (8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
  unfold squareC
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (pipe_ok h0 tab_sq) fun s3 h3 => ?_)
  have hsum := sqCols_sum fun i => dw s0.mem A (8 * i)
  have hlt : colsV (fun i => dw s0.mem A (8 * i)) 9 * colsV (fun i => dw s0.mem A (8 * i)) 9 < (2 ^ 64) ^ 18 := by
    rw [show (18 : Nat) = 9 + 9 from rfl, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (GenWide.colsV_lt _ (fun _ => hX _) 9) (GenWide.colsV_lt _ (fun _ => hX _) 9)
  have hfin : pw s3.mem b 0 18 = colsV (sqCs fun i => dw s0.mem A (8 * i)) 18 :=
    h3.final (by rw [sqCs_eq]) (by omega)
  refine wp_li (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => ?_
  have hI5 : TInv b s0 s5 := h3.t.keeps (rs := [.a5, .a4])
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u5.other _ hr.2, u4.other _ hr.1], by rw [u5.mem, u4.mem], by rw [u5.rd, u4.rd], by rw [u5.wr, u4.wr],
      by rw [u5.sp, u4.sp]⟩ (by decide)
  have hm5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  have hd0 : DblInv b A s0 (fun i => dw s3.mem b (P + 8 * i)) 0 s5 :=
    ⟨hI5, fun i _ _ => by rw [hm5], by rw [u5.other _ (by decide), u4.gpr]; rfl, fun h' => absurd h' (by decide),
      by rw [u5.gpr]; decide, by rw [u5.gpr]; rfl⟩
  refine WP.mono (dbls_ok h0 (fun i => dw_lt _ _ _) 18 (Nat.le_refl _) s5 hd0) fun s6 h6 =>
    ⟨h6.t.gpr, h6.t.rd, h6.t.wr, h6.t.sp, h6.t.frame, ?_⟩
  have hv := h6.val
  rw [colsV_add, colsV_dq] at hv
  have hd := colsV_dbw (C := fun i => dw s3.mem b (P + 8 * i)) (fun i => dw_lt _ _ _) 17
  have hW3 : pw s3.mem b 0 18 = colsV (fun i => dw s3.mem b (P + 8 * i)) 18 :=
    colsV_congr fun i _ => by rw [show P + 8 * 0 + 8 * i = P + 8 * i by omega]
  rw [← hW3, hfin] at hd
  have hW6 : pw s6.mem b 0 18 = colsV (fun i => dw s6.mem b (P + 8 * i)) 18 :=
    colsV_congr fun i _ => by rw [show P + 8 * 0 + 8 * i = P + 8 * i by omega]
  rw [hW6]
  have := GenWide.colsV_lt (fun i => dw s6.mem b (P + 8 * i)) (fun _ => dw_lt _ _ _) 18
  show colsV _ 18 = colsV (fun j => dw s0.mem A (8 * j)) 9 * colsV (fun j => dw s0.mem A (8 * j)) 9
  generalize (2 ^ 64) ^ 18 = K at *
  generalize colsV (fun i => dw s6.mem b (P + 8 * i)) 18 = W at *
  generalize colsV (fun i => dw s0.mem A (8 * i)) 9 * colsV (fun i => dw s0.mem A (8 * i)) 9 = Q at *
  generalize colsV (dbw fun i => dw s3.mem b (P + 8 * i)) 18 = D at *
  generalize colsV (sqCs fun i => dw s0.mem A (8 * i)) 18 = S at *
  generalize dsq (fun i => dw s0.mem A (8 * i)) = E at *
  generalize (s6.gpr .a4).toNat = c at *
  generalize dw s3.mem b (P + 8 * 17) / 2 ^ 63 = t at *
  rcases Nat.eq_zero_or_pos (c + t) with h0 | hpos
  · have : c = 0 := by omega
    have : t = 0 := by omega
    subst_vars; omega
  · have : K ≤ K * (c + t) := Nat.le_mul_of_pos_right _ hpos
    rw [Nat.mul_add] at this
    omega

end

end

/-! ## Bits of words -/

theorem wp_srl {s : State} {is : List Instr} {Q : State → Prop} {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .srl .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_sll {s : State} {is : List Instr} {Q : State → Prop} {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sll .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

/-- `(x >> s) | (y << t)`, `s + t = 64`, is `x / 2^s + (y mod 2^s) 2^t`. -/
theorem shr_or_shl (x y : BitVec 64) {s t : Nat} (hst : s + t = 64) :
    ((x >>> s) ||| (y <<< t)).toNat = x.toNat / 2 ^ s + y.toNat % 2 ^ s * 2 ^ t := by
  have hx := x.isLt
  have e64 : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ t := by rw [← Nat.pow_add, hst]
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, e64, Nat.mul_mod_mul_right]
  have hlt : x.toNat / 2 ^ s < 2 ^ t := Nat.div_lt_of_lt_mul (by rw [← e64]; exact hx)
  rw [Nat.or_comm, Nat.mul_comm (y.toNat % 2 ^ s), ← Nat.two_pow_add_eq_or_of_lt hlt]
  omega

/-- `x &&& 511` is `x mod 2^9`. -/
theorem and511 (x : BitVec 64) : (x &&& BitVec.ofInt 64 0x1ff).toNat = x.toNat % 2 ^ 9 := by
  rw [show BitVec.ofInt 64 0x1ff = BitVec.ofNat 64 (2 ^ 9 - 1) from rfl, BitVec.toNat_and,
    BitVec.toNat_ofNat, show (2 ^ 9 - 1) % 2 ^ 64 = 2 ^ 9 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The words of a number shifted right by `s` bits: `2^s` times their
number, plus the low bits, is the number plus the low bits of the next word. -/
theorem shr_cols (w : Nat → Nat) {s : Nat} (hs : s ≤ 64) : ∀ n,
    2 ^ s * colsV (fun i => w i / 2 ^ s + w (i + 1) % 2 ^ s * 2 ^ (64 - s)) n + w 0 % 2 ^ s =
      colsV w n + (2 ^ 64) ^ n * (w n % 2 ^ s)
  | 0 => by simp [colsV]
  | n + 1 => by
    have ih := shr_cols w hs n
    have e : (2 : Nat) ^ s * 2 ^ (64 - s) = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
    simp only [colsV]
    have h1 := Nat.div_add_mod (w n) (2 ^ s)
    rw [show (2 ^ 64) ^ (n + 1) = (2 ^ 64) ^ n * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ n = E at *
    generalize w n / 2 ^ s = A at *
    generalize w (n + 1) % 2 ^ s = Bq
    generalize hS : 2 ^ s = S at *
    generalize 2 ^ (64 - s) = U at *
    have h3 : S * (E * (A + Bq * U)) = E * (S * A) + E * (S * U) * Bq := by
      rw [Nat.mul_add E, Nat.mul_add S]; ac_rfl
    rw [e] at h3
    have h2 : E * (S * A) + E * (w n % S) = E * w n := by rw [← Nat.mul_add, h1]
    rw [Nat.mul_add, h3]
    omega

/-! ## Carries through the words -/

/-- After `j` steps of `+ a5` from `s0`. -/
structure CarryInv (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.t0, .a5] → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 P, 8 * j⟩] s0.mem s.mem
  cy : 0 < j → (s.gpr .a5).toNat ≤ 1
  val : pw s.mem b 0 j + (2 ^ 64) ^ j * (s.gpr .a5).toNat = pw s0.mem b 0 j + (s0.gpr .a5).toNat

set_option linter.unusedSimpArgs false in
theorem carryStep_ok {b : Addr} {s0 : State} (hc : Ctx b s0) {j : Nat} (hj : j < 9) {s : State}
    (h : CarryInv b s0 j s) : WP isa (.block (carryStep j)) s (CarryInv b s0 (j + 1)) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  have hal := hc.al
  unfold carryStep
  refine ld_ok hcs (by omega) (by omega) fun s1 u1 => wp_add fun s2 u2 => wp_sltu fun s3 u3 => ?_
  have hc3 : Ctx b s3 := ctx_of hcs (by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)])
    (by rw [u3.wr, u2.wr, u1.wr])
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  have t0 : s3.gpr .t0 = s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5 := by
    rw [u3.other _ (by decide), u2.gpr, u1.gpr, u1.other _ (by decide)]
  have a5 : s3.gpr .a5 = if s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5 < s.gpr .a5 then 1 else 0 := by
    rw [u3.gpr, u2.gpr, u2.other _ (by decide), u1.gpr, u1.other _ (by decide)]
  have hm4 : s4.mem = s.mem.writeW (b + BitVec.ofNat 64 (P + 8 * j)) (s3.gpr .t0) := by
    rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have e := carry (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64) (s.gpr .a5)
  have hw0 : dw s.mem b (P + 8 * j) = dw s0.mem b (P + 8 * j) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
  refine ⟨fun r hr => ?_, by rw [u4.rd, u3.rd, u2.rd, u1.rd, h.rd], by rw [u4.wr, u3.wr, u2.wr, u1.wr, h.wr],
    by rw [u4.sp, u3.sp, u2.sp, u1.sp, h.sp], ?_, fun _ => by rw [u4.gpr, a5]; exact carry_le _, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u4.gpr, u3.other _ hr.2, u2.other _ hr.1, u1.other _ hr.1, h.gpr r (by simp [hr.1, hr.2])]
  · rw [hm4]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · have hv := h.val
    have hcw : pw s4.mem b 0 j = pw s.mem b 0 j :=
      colsV_congr fun i hi => by rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    show pw s4.mem b 0 j + (2 ^ 64) ^ j * dw s4.mem b (P + 8 * 0 + 8 * j) + (2 ^ 64) ^ (j + 1) * (s4.gpr .a5).toNat =
      pw s0.mem b 0 j + (2 ^ 64) ^ j * dw s0.mem b (P + 8 * 0 + 8 * j) + (s0.gpr .a5).toNat
    rw [hcw, show P + 8 * 0 + 8 * j = P + 8 * j by omega, hm4, dw_write_self, u4.gpr, t0, a5, ← hw0,
      show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    have key : E * (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5).toNat +
        E * 2 ^ 64 * (if s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5 < s.gpr .a5
          then (1 : BitVec 64) else 0).toNat =
        E * dw s.mem b (P + 8 * j) + E * (s.gpr .a5).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, e, Nat.mul_add]; rfl
    omega

theorem carry_ok {b : Addr} {s0 : State} (hc : Ctx b s0) :
    ∀ j ≤ 9, WP isa (.block ((List.range j).flatMap carryStep)) s0 (CarryInv b s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun h => absurd h (Nat.lt_irrefl _),
      by simp [colsV]⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (carry_ok hc j (by omega)) fun s h => carryStep_ok hc (by omega) h)

/-! ## The first fold -/

/-- Word `j` of `T >> 521` into `a7`. -/
theorem hiWord_ok {b : Addr} {s : State} (hc : Ctx b s) {j : Nat} (hj : j ≤ 8) :
    WP isa (.block (hiWord j)) s fun s' =>
      (s'.gpr .a7).toNat = dw s.mem b (P + 8 * (8 + j)) / 2 ^ 9 + dw s.mem b (P + 8 * (9 + j)) % 2 ^ 9 * 2 ^ 55 ∧
      (∀ r, r ∉ [Reg.t0, .a7] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  have hP := P_eq
  unfold hiWord
  refine ld_ok hc (by omega) (by omega) fun s1 u1 =>
    ld_ok (ctx_of hc (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 =>
    wp_srl (by decide) fun s3 u3 => wp_sll (by decide) fun s4 u4 => wp_or fun s5 u5 => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem], by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr], by rw [u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]⟩
  · rw [u5.gpr, u4.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.gpr,
      u2.gpr, u1.mem, shr_or_shl _ _ (by decide : 9 + 55 = 64)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u5.other _ hr.2, u4.other _ hr.1, u3.other _ hr.2, u2.other _ hr.1, u1.other _ hr.2]

/-- The registers the fold writes. -/
abbrev clobF : List Reg := [.t0, .t3, .a5, .a6, .a7]

/-- Word `i` of `T >> 521`, from the words of `T` at `s0`. -/
abbrev hw (m : Mem) (b : Addr) (i : Nat) : Nat :=
  dw m b (P + 8 * (8 + i)) / 2 ^ 9 + dw m b (P + 8 * (9 + i)) % 2 ^ 9 * 2 ^ 55

/-- Word `i` of `T mod 2⁵²¹`. -/
abbrev lw (m : Mem) (b : Addr) (i : Nat) : Nat :=
  if i < 8 then dw m b (P + 8 * i) else dw m b (P + 8 * i) % 2 ^ 9

/-- After `j` words of the fold from `s0`. -/
structure FoldInv (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobF → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 P, 8 * j⟩] s0.mem s.mem
  cy : (s.gpr .a5).toNat ≤ 1
  val : pw s.mem b 0 j + (2 ^ 64) ^ j * (s.gpr .a5).toNat =
    colsV (fun i => lw s0.mem b i + hw s0.mem b i) j + (s0.gpr .a5).toNat

set_option linter.unusedSimpArgs false in
/-- The end of a word of the fold: `a6 + a7 + a5`, for `a6` the low word and
`a7` `T >> 521`'s, into word `j`. -/
theorem foldTail_ok {b : Addr} {s0 s : State} (hc : Ctx b s0) {j : Nat} (hj : j ≤ 8) (h : FoldInv b s0 j s)
    {s1 : State} (m1 : s1.mem = s.mem) (rd1 : s1.rd = s.rd) (wr1 : s1.wr = s.wr) (sp1 : s1.sp = s.sp)
    (g1 : ∀ r, r ∉ [Reg.t0, .a6, .a7] → s1.gpr r = s.gpr r)
    (a6 : (s1.gpr .a6).toNat = lw s0.mem b j) (a7 : (s1.gpr .a7).toNat = hw s0.mem b j) :
    WP isa (.block (adcCore ++ ([.store .d .t0 .a3 (P + 8 * j)] : List Instr))) s1 (FoldInv b s0 (j + 1)) := by
  have hP := P_eq
  have hal := hc.al
  have hc1 : Ctx b s1 := ctx_of hc (by rw [g1 _ (by decide), h.gpr _ (by decide)]) (by rw [wr1, h.wr])
  refine WP.block_append (WP.mono (adc_ok (d := .t0) (x := .a6) (y := .a7) (c := .a5) (u := .t3))
    fun s4 ⟨e4, k4⟩ => ?_)
  have hc4 : Ctx b s4 := ctx_of hc1 (k4.1 _ (by decide)) k4.2.2.2.1
  refine sd_ok hc4 (by omega) (by omega) fun s5 u5 => WP.block_nil ?_
  have a5 : s1.gpr .a5 = s.gpr .a5 := g1 _ (by decide)
  have e4v := e4 (by rw [a5]; exact h.cy)
  have hm5 : s5.mem = s.mem.writeW (b + BitVec.ofNat 64 (P + 8 * j)) (s4.gpr .t0) := by
    rw [u5.mem, k4.2.1, m1]
  refine ⟨fun r hr => ?_, by rw [u5.rd, k4.2.2.1, rd1, h.rd], by rw [u5.wr, k4.2.2.2.1, wr1, h.wr],
    by rw [u5.sp, k4.2.2.2.2, sp1, h.sp], ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u5.gpr, k4.1 r (by simp [hr.1, hr.2.1, hr.2.2.1]), g1 r (by simp [hr.1, hr.2.2.2.1, hr.2.2.2.2]),
      h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  · rw [hm5]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · rw [u5.gpr]
    have := (s1.gpr .a6).isLt; have := (s1.gpr .a7).isLt; have := h.cy
    rw [← a5] at this
    omega
  · have hv := h.val
    have hcw : pw s5.mem b 0 j = pw s.mem b 0 j :=
      colsV_congr fun i hi => by rw [hm5, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    rw [a6, a7, a5] at e4v
    show pw s5.mem b 0 j + (2 ^ 64) ^ j * dw s5.mem b (P + 8 * 0 + 8 * j) + (2 ^ 64) ^ (j + 1) * (s5.gpr .a5).toNat =
      colsV (fun i => lw s0.mem b i + hw s0.mem b i) j + (2 ^ 64) ^ j * (lw s0.mem b j + hw s0.mem b j) +
        (s0.gpr .a5).toNat
    rw [hcw, show P + 8 * 0 + 8 * j = P + 8 * j by omega, hm5, dw_write_self, u5.gpr,
      show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    have key : E * (s4.gpr .t0).toNat + E * 2 ^ 64 * (s4.gpr .a5).toNat =
        E * (lw s0.mem b j + hw s0.mem b j) + E * (s.gpr .a5).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, e4v, Nat.mul_add]
    omega

theorem fold_word {b : Addr} {s0 s : State} {j i : Nat} (h : FoldInv b s0 j s) (hj : j ≤ i) (hi : i ≤ 17) :
    dw s.mem b (P + 8 * i) = dw s0.mem b (P + 8 * i) := by
  have hP := P_eq
  exact dw_frame h.frame fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)

/-- Word `j < 8` of the fold. -/
theorem foldStep_ok {b : Addr} {s0 : State} (hc : Ctx b s0) {j : Nat} (hj : j < 8) {s : State}
    (h : FoldInv b s0 j s) : WP isa (.block (foldStep j)) s (FoldInv b s0 (j + 1)) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  unfold foldStep
  rw [List.append_assoc, List.append_assoc, List.singleton_append]
  refine WP.block_append (WP.mono (hiWord_ok hcs (j := j) (by omega)) fun s1 ⟨a7, g1, m1, rd1, wr1, sp1⟩ => ?_)
  refine ld_ok (ctx_of hcs (g1 _ (by decide)) wr1) (by omega) (by omega) fun s2 u2 => ?_
  refine foldTail_ok hc (by omega) h (by rw [u2.mem, m1]) (by rw [u2.rd, rd1]) (by rw [u2.wr, wr1])
    (by rw [u2.sp, sp1]) (fun r hr => ?_) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u2.other _ hr.2.1, g1 r (by simp [hr.1, hr.2.2])]
  · rw [u2.gpr, m1, show lw s0.mem b j = dw s0.mem b (P + 8 * j) from ite_eq_left hj, ← fold_word h (Nat.le_refl _) (by omega)]
    rfl
  · rw [u2.other _ (by decide), a7, fold_word h (by omega) (by omega), fold_word h (by omega) (by omega)]

/-- Word 8 of the fold. -/
theorem foldTop_ok {b : Addr} {s0 : State} (hc : Ctx b s0) {s : State}
    (h : FoldInv b s0 8 s) : WP isa (.block foldTop) s (FoldInv b s0 9) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  unfold foldTop
  rw [List.append_assoc, List.append_assoc, List.cons_append, List.singleton_append]
  refine WP.block_append (WP.mono (hiWord_ok hcs (j := 8) (by omega)) fun s1 ⟨a7, g1, m1, rd1, wr1, sp1⟩ => ?_)
  refine ld_ok (ctx_of hcs (g1 _ (by decide)) wr1) (by omega) (by omega) fun s2 u2 => wp_andi (by decide) fun s3 u3 => ?_
  refine foldTail_ok hc (by omega) h (by rw [u3.mem, u2.mem, m1]) (by rw [u3.rd, u2.rd, rd1])
    (by rw [u3.wr, u2.wr, wr1]) (by rw [u3.sp, u2.sp, sp1]) (fun r hr => ?_) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u3.other _ hr.2.1, u2.other _ hr.2.1, g1 r (by simp [hr.1, hr.2.2])]
  · rw [u3.gpr, and511, u2.gpr, m1, show lw s0.mem b 8 = dw s0.mem b (P + 8 * 8) % 2 ^ 9 from ite_eq_right (by omega),
      ← fold_word h (Nat.le_refl _) (by omega)]
    rfl
  · rw [u3.other _ (by decide), u2.other _ (by decide), a7, fold_word h (by omega) (by omega),
      fold_word h (by omega) (by omega)]

/-- The fold: `s`'s nine words and its carry. -/
theorem fold_ok {b : Addr} {s0 : State} (hc : Ctx b s0) :
    WP isa (.block fold) s0 fun s => (∀ r, r ∉ clobF → s.gpr r = s0.gpr r) ∧ s.rd = s0.rd ∧ s.wr = s0.wr ∧
      s.sp = s0.sp ∧ Frame [⟨b + BitVec.ofNat 64 P, 72⟩] s0.mem s.mem ∧ (s.gpr .a5).toNat ≤ 1 ∧
      pw s.mem b 0 9 + 2 ^ 576 * (s.gpr .a5).toNat = colsV (fun i => lw s0.mem b i + hw s0.mem b i) 9 := by
  unfold fold
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := ctx_of hc (u1.other _ (by decide)) u1.wr
  have steps : ∀ j ≤ 8, WP isa (.block ((List.range j).flatMap foldStep)) s1 (FoldInv b s1 j) := fun j hj => by
    induction j with
    | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, by rw [u1.gpr]; decide, by simp [colsV]⟩
    | succ j ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact WP.block_append (WP.mono (ih (by omega)) fun s h => foldStep_ok hc1 (by omega) h)
  refine WP.block_append (WP.mono (steps 8 (Nat.le_refl _)) fun s h => ?_)
  refine WP.mono (foldTop_ok hc1 h) fun s' h' => ?_
  have a50 : (s1.gpr .a5).toNat = 0 := by rw [u1.gpr]; rfl
  have m1 : s1.mem = s0.mem := u1.mem
  refine ⟨fun r hr => by
      rw [h'.gpr r hr, u1.other r (fun e => hr (by rw [e]; decide))],
    by rw [h'.rd, u1.rd], by rw [h'.wr, u1.wr], by rw [h'.sp, u1.sp], by rw [← m1]; exact h'.frame, h'.cy, ?_⟩
  have hv := h'.val
  rw [a50, Nat.add_zero, m1] at hv
  exact hv

/-! ## The second fold -/

/-- `(s₈ >> 9) | (c << 55)` into `a5`, `s₈` cut to its nine bits, then the
carries: the nine words become `s mod 2⁵²¹ + s >> 521`. -/
theorem fold2_ok {b : Addr} {s : State} (hc : Ctx b s) (hc5 : (s.gpr .a5).toNat ≤ 1) :
    WP isa (.block fold2) s fun s' => (∀ r, r ∉ [Reg.t0, .a5, .a6] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨b + BitVec.ofNat 64 P, 72⟩] s.mem s'.mem ∧
      pw s'.mem b 0 9 + 2 ^ 576 * (s'.gpr .a5).toNat =
        pw s.mem b 0 8 + 2 ^ 512 * (dw s.mem b (P + 64) % 2 ^ 9) + (dw s.mem b (P + 64) / 2 ^ 9 +
          (s.gpr .a5).toNat * 2 ^ 55) := by
  have hP := P_eq
  have hal := hc.al
  unfold fold2
  rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append]
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => wp_srl (by decide) fun s2 u2 => wp_sll (by decide) fun s3 u3 =>
    wp_or fun s4 u4 => wp_andi (by decide) fun s5 u5 => ?_
  have hc5' : Ctx b s5 := ctx_of hc (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
    u2.other _ (by decide), u1.other _ (by decide)]) (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine sd_ok hc5' (by omega) (by omega) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := ctx_of hc5' (by rw [u6.gpr]) u6.wr
  have x8 : (s.mem.readW (b + BitVec.ofNat 64 (P + 64)) 64).toNat = dw s.mem b (P + 64) := rfl
  have a5v : (s6.gpr .a5).toNat = dw s.mem b (P + 64) / 2 ^ 9 + (s.gpr .a5).toNat * 2 ^ 55 := by
    rw [u6.gpr, u5.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide), u2.gpr, u2.other _ (by decide),
      u1.gpr, u1.other _ (by decide), BitVec.or_comm, shr_or_shl _ _ (by decide : 9 + 55 = 64), x8,
      Nat.mod_eq_of_lt (by omega : (s.gpr .a5).toNat < 2 ^ 9)]
  have hm6 : s6.mem = s.mem.writeW (b + BitVec.ofNat 64 (P + 64)) (s5.gpr .t0) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have t05 : (s5.gpr .t0).toNat = dw s.mem b (P + 64) % 2 ^ 9 := by
    rw [u5.gpr, and511, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
  refine WP.mono (carry_ok hc6 9 (Nat.le_refl _))
    fun s' h' => ⟨fun r hr => ?_, by rw [h'.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
      by rw [h'.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr], by rw [h'.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp],
      ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h'.gpr r (by simp [hr.1, hr.2.1]), u6.gpr, u5.other _ hr.1, u4.other _ hr.2.1, u3.other _ hr.2.1,
      u2.other _ hr.2.2, u1.other _ hr.1]
  · have f := h'.frame
    rw [hm6] at f
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))).trans f
  · have hv := h'.val
    rw [a5v] at hv
    rw [hv]
    have hlow : pw s6.mem b 0 8 = pw s.mem b 0 8 :=
      colsV_congr fun i hi => by rw [hm6, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have htop : dw s6.mem b (P + 8 * 0 + 8 * 8) = dw s.mem b (P + 64) % 2 ^ 9 := by
      rw [hm6, show P + 8 * 0 + 8 * 8 = P + 64 by omega, dw_write_self, t05]
    show pw s6.mem b 0 8 + (2 ^ 64) ^ 8 * dw s6.mem b (P + 8 * 0 + 8 * 8) + _ = _
    rw [hlow, htop]

/-! ## The correction -/

theorem pw_lt (m : Mem) (b : Addr) (n : Nat) : pw m b 0 n < (2 ^ 64) ^ n :=
  GenWide.colsV_lt _ (fun _ => dw_lt _ _ _) n

/-- After `j` words of the carry of `+ a5` from `s0`, not stored. -/
structure ProbeInv (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.t0, .a5] → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : (s.gpr .a5).toNat = (pw s0.mem b 0 j + (s0.gpr .a5).toNat) / (2 ^ 64) ^ j

theorem probeStep_ok {b : Addr} {s0 : State} (hc : Ctx b s0) {j : Nat} (hj : j < 9) {s : State}
    (h : ProbeInv b s0 j s) : WP isa (.block (probeStep j)) s (ProbeInv b s0 (j + 1)) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  unfold probeStep
  refine ld_ok hcs (by omega) (by omega) fun s1 u1 => wp_add fun s2 u2 => wp_sltu fun s3 u3 => WP.block_nil ?_
  have e := carry (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64) (s.gpr .a5)
  refine ⟨fun r hr => ?_, by rw [u3.mem, u2.mem, u1.mem, h.mem], by rw [u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u3.wr, u2.wr, u1.wr, h.wr], by rw [u3.sp, u2.sp, u1.sp, h.sp], ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u3.other _ hr.2, u2.other _ hr.1, u1.other _ hr.1, h.gpr r (by simp [hr.1, hr.2])]
  · rw [u3.gpr, u2.gpr, u2.other _ (by decide), u1.gpr, u1.other _ (by decide)]
    have hv := h.val
    have hw : (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64).toNat = dw s0.mem b (P + 8 * 0 + 8 * j) := by
      rw [h.mem, show P + 8 * 0 + 8 * j = P + 8 * j by omega]; rfl
    rw [hw] at e
    have hlt := (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5).isLt
    generalize (if s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5 < s.gpr .a5
      then (1 : BitVec 64) else 0) = c at *
    generalize (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5) = t0 at *
    show c.toNat = (pw s0.mem b 0 j + (2 ^ 64) ^ j * dw s0.mem b (P + 8 * 0 + 8 * j) + (s0.gpr .a5).toNat) /
      (2 ^ 64) ^ (j + 1)
    rw [show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ .., ← Nat.div_div_eq_div_mul,
      Nat.add_right_comm, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), ← hv]
    omega

theorem probe_ok {b : Addr} {s0 : State} (hc : Ctx b s0) :
    ∀ j ≤ 9, WP isa (.block ((List.range j).flatMap probeStep)) s0 (ProbeInv b s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, by simp [colsV]⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (probe_ok hc j (by omega)) fun s h => probeStep_ok hc (by omega) h)

theorem pw_succ (m : Mem) (b : Addr) (n : Nat) :
    pw m b 0 (n + 1) = pw m b 0 n + (2 ^ 64) ^ n * dw m b (P + 8 * n) := by
  show pw m b 0 n + (2 ^ 64) ^ n * dw m b (P + 8 * 0 + 8 * n) = _
  rw [show P + 8 * 0 + 8 * n = P + 8 * n by omega]

/-- `r = (s₂ + q) mod 2⁵²¹`, `q` the bit 521 of `s₂ + 1`. -/
theorem canon_ok {b : Addr} {s : State} (hc : Ctx b s) (hs : pw s.mem b 0 9 < 2 ^ 521 + 2 ^ 56) :
    WP isa (.block canon) s fun s' => (∀ r, r ∉ [Reg.t0, .a5] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨b + BitVec.ofNat 64 P, 72⟩] s.mem s'.mem ∧
      pw s'.mem b 0 9 = (pw s.mem b 0 9 + (pw s.mem b 0 9 + 1) / 2 ^ 521) % 2 ^ 521 := by
  have hP := P_eq
  have hal := hc.al
  unfold canon
  show WP isa (.block (Instr.li .a5 1 :: ((List.range 8).flatMap probeStep ++
    (Instr.load .d .t0 .a3 (P + 64) :: Instr.add .t0 .t0 .a5 :: Instr.shift .srl .d .a5 .t0 9 ::
      ((List.range 9).flatMap carryStep ++ [Instr.load .d .t0 .a3 (P + 64), .logicImm .and .t0 .t0 0x1ff,
        .store .d .t0 .a3 (P + 64)]))))) s _
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := ctx_of hc (u1.other _ (by decide)) u1.wr
  refine WP.block_append (WP.mono (probe_ok hc1 8 (by omega)) fun s2 h2 => ?_)
  have hc2 : Ctx b s2 := ctx_of hc1 (h2.gpr _ (by decide)) h2.wr
  refine ld_ok hc2 (by omega) (by omega) fun s3 u3 => wp_add fun s4 u4 => wp_srl (by decide) fun s5 u5 => ?_
  have hc5 : Ctx b s5 := ctx_of hc2 (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide)])
    (by rw [u5.wr, u4.wr, u3.wr])
  refine WP.block_append (WP.mono (carry_ok hc5 9 (Nat.le_refl _)) fun s6 h6 => ?_)
  have hc6 : Ctx b s6 := ctx_of hc5 (h6.gpr _ (by decide)) h6.wr
  refine ld_ok hc6 (by omega) (by omega) fun s7 u7 => wp_andi (by decide) fun s8 u8 => ?_
  have hc8 : Ctx b s8 := ctx_of hc6 (by rw [u8.other _ (by decide), u7.other _ (by decide)]) (by rw [u8.wr, u7.wr])
  refine sd_ok hc8 (by omega) (by omega) fun s9 u9 => WP.block_nil ?_
  -- Memory.
  have m1 : s1.mem = s.mem := u1.mem
  have m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, h2.mem, m1]
  have m8 : s8.mem = s6.mem := by rw [u8.mem, u7.mem]
  have hm9 : s9.mem = s6.mem.writeW (b + BitVec.ofNat 64 (P + 64)) (s8.gpr .t0) := by rw [u9.mem, m8]
  -- The values.
  generalize hS : pw s.mem b 0 9 = S at hs ⊢
  have hS8 : pw s.mem b 0 9 = pw s.mem b 0 8 + (2 ^ 64) ^ 8 * dw s.mem b (P + 8 * 8) := pw_succ s.mem b 8
  rw [hS] at hS8
  have h8lt := pw_lt s.mem b 8
  have hw8 : dw s.mem b (P + 8 * 8) < 2 ^ 10 := by omega
  have c8 : (s2.gpr .a5).toNat = (pw s.mem b 0 8 + 1) / 2 ^ 512 := by
    rw [h2.val, m1, u1.gpr]; rfl
  have c8le : (s2.gpr .a5).toNat ≤ 1 := by rw [c8]; omega
  have hq : (s5.gpr .a5).toNat = (S + 1) / 2 ^ 521 := by
    rw [u5.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, u4.gpr, u3.gpr,
      u3.other _ (by decide : Reg.a5 ≠ Reg.t0), BitVec.toNat_add, h2.mem, m1, c8]
    show ((dw s.mem b (P + 8 * 8)) + (pw s.mem b 0 8 + 1) / 2 ^ 512) % 2 ^ 64 / 2 ^ 9 = _
    rw [Nat.mod_eq_of_lt (by omega), hS8, Nat.add_right_comm, show (2 : Nat) ^ 521 = 2 ^ 512 * 2 ^ 9 by decide,
      ← Nat.div_div_eq_div_mul, show (2 ^ 64) ^ 8 = (2 : Nat) ^ 512 by decide,
      Nat.add_mul_div_left _ _ (by decide), Nat.add_comm]
  have v6 := h6.val
  rw [m5, hS, hq] at v6
  have h6lt := pw_lt s6.mem b 9
  have hq1 : (S + 1) / 2 ^ 521 ≤ 1 := by omega
  have c6 : (s6.gpr .a5).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (s6.gpr .a5).toNat with h | h
    · exact h
    · exfalso; have : (2 : Nat) ^ 576 = (2 ^ 64) ^ 9 := by decide
      omega
  rw [c6, Nat.mul_zero, Nat.add_zero] at v6
  have t08 : (s8.gpr .t0).toNat = dw s6.mem b (P + 64) % 2 ^ 9 := by
    rw [u8.gpr, and511, u7.gpr]; rfl
  have h68 : pw s6.mem b 0 9 = pw s6.mem b 0 8 + (2 ^ 64) ^ 8 * dw s6.mem b (P + 8 * 8) := pw_succ s6.mem b 8
  have h6lt8 := pw_lt s6.mem b 8
  have hlow : pw s9.mem b 0 8 = pw s6.mem b 0 8 :=
    colsV_congr fun i hi => by rw [hm9, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
  have h98 : pw s9.mem b 0 9 = pw s9.mem b 0 8 + (2 ^ 64) ^ 8 * dw s9.mem b (P + 8 * 8) := pw_succ s9.mem b 8
  have d9 : dw s9.mem b (P + 8 * 8) = dw s6.mem b (P + 64) % 2 ^ 9 := by
    rw [hm9, show P + 8 * 8 = P + 64 from rfl, dw_write_self, t08]
  rw [hlow, d9] at h98
  rw [show P + 8 * 8 = P + 64 from rfl] at h68
  refine ⟨fun r hr => ?_, by rw [u9.rd, u8.rd, u7.rd, h6.rd, u5.rd, u4.rd, u3.rd, h2.rd, u1.rd],
    by rw [u9.wr, u8.wr, u7.wr, h6.wr, u5.wr, u4.wr, u3.wr, h2.wr, u1.wr],
    by rw [u9.sp, u8.sp, u7.sp, h6.sp, u5.sp, u4.sp, u3.sp, h2.sp, u1.sp], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u9.gpr, u8.other _ hr.1, u7.other _ hr.1, h6.gpr r (by simp [hr.1, hr.2]), u5.other _ hr.2,
      u4.other _ hr.1, u3.other _ hr.1, h2.gpr r (by simp [hr.1, hr.2]), u1.other _ hr.2]
  · have f := h6.frame
    rw [m5] at f
    rw [hm9]
    exact f.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))
  · rw [h98]
    have : (2 ^ 64) ^ 8 = (2 : Nat) ^ 512 := by decide
    rw [this] at h68 ⊢
    omega

/-! ## The rotation -/

/-- `x | (y << 18)` for `x < 2^18`. -/
theorem or_shl18 (x y : BitVec 64) (hx : x.toNat < 2 ^ 18) :
    (x ||| (y <<< 18)).toNat = x.toNat + y.toNat % 2 ^ 46 * 2 ^ 18 := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    show (2 : Nat) ^ 64 = 2 ^ 46 * 2 ^ 18 by decide, Nat.mul_mod_mul_right,
    Nat.mul_comm (y.toNat % 2 ^ 46), Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hx]
  omega

/-- What the rotation needs of `[o]`. -/
structure OCtx (b O : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  o : s.gpr .t2 = O
  oal : O.toNat % 8 = 0
  ow : ∀ i < 9, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8
  onw : O.toNat + 72 ≤ 2 ^ 64
  odis : Region.Disjoint ⟨O, 72⟩ (own b)

/-- Word `i` of `r` rotated, for `i < 8`, from `r`'s words. -/
abbrev rw' (m : Mem) (b : Addr) (i : Nat) : Nat :=
  dw m b (P + 8 * i) / 2 ^ 55 + dw m b (P + 8 * (i + 1)) % 2 ^ 55 * 2 ^ 9

/-- After `j` words of the rotation from `s0`. -/
structure RotInv (b O : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.t0, .a6] → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 8 * j⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem O (8 * i) = rw' s0.mem b i

theorem own_of_frame {b O : Addr} {s0 : State} (hO : OCtx b O s0) {n : Nat} (hn : n ≤ 72) {m : Mem}
    (f : Frame [⟨O, n⟩] s0.mem m) {d : Nat} (hd : P ≤ d) (hd' : d + 8 ≤ P + 160) : dw m b d = dw s0.mem b d :=
  dw_frame f fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact GenWide.disj_mono (GenWide.disj_symm (GenWide.disj_sub hO.odis (own_sub hd hd'))) hn

theorem own_of_rot {b O : Addr} {s0 s : State} (hO : OCtx b O s0) {j : Nat} (hj : j ≤ 9) (h : RotInv b O s0 j s)
    {d : Nat} (hd : P ≤ d) (hd' : d + 8 ≤ P + 160) : dw s.mem b d = dw s0.mem b d :=
  own_of_frame hO (by omega) h.frame hd hd'

/-- `(r_j >> 55) | (r_{j+1} << 9)` into `t0`. -/
theorem rotWord_ok {b : Addr} {s : State} (hc : Ctx b s) {j : Nat} (hj : j < 8) :
    WP isa (.block (rotWord j)) s fun s' =>
      (s'.gpr .t0).toNat = rw' s.mem b j ∧ (∀ r, r ∉ [Reg.t0, .a6] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hP := P_eq
  unfold rotWord
  refine ld_ok hc (by omega) (by omega) fun s1 u1 =>
    ld_ok (ctx_of hc (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 =>
    wp_srl (by decide) fun s3 u3 => wp_sll (by decide) fun s4 u4 => wp_or fun s5 u5 => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem], by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr], by rw [u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]⟩
  · rw [u5.gpr, u4.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.gpr,
      u2.gpr, u1.mem, shr_or_shl _ _ (by decide : 55 + 9 = 64)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u5.other _ hr.1, u4.other _ hr.2, u3.other _ hr.1, u2.other _ hr.2, u1.other _ hr.1]

/-- `[o + d] := t0` for a word `d / 8 < 9` of `[o]`. -/
theorem rot_store {b O : Addr} {s0 s : State} (hO : OCtx b O s0) {j : Nat} (h : RotInv b O s0 j s)
    {s1 : State} {is : List Instr} {Q : State → Prop} (hj : j < 9)
    (g1 : ∀ r, r ∉ [Reg.t0, .a6] → s1.gpr r = s.gpr r) (wr1 : s1.wr = s.wr)
    (k : ∀ s', Mupd s1 s' (s1.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s1.gpr .t0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d .t0 .t2 (8 * j) :: is)) s1 Q :=
  wp_sd (by omega) (by rw [g1 _ (by decide), h.gpr _ (by decide), hO.o]) (al8 hO.oal (by omega))
    (by rw [wr1, h.wr]; exact hO.ow j hj) k

/-- The frame and the words after a store of word `j`. -/
theorem rot_next {b O : Addr} {s0 s : State} (hO : OCtx b O s0) {j : Nat} (hj : j < 9) (h : RotInv b O s0 j s)
    {s' : State} {v : BitVec 64} (hm : s'.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) v) :
    Frame [⟨O, 8 * (j + 1)⟩] s0.mem s'.mem ∧ (∀ i < j, dw s'.mem O (8 * i) = rw' s0.mem b i) ∧
      dw s'.mem O (8 * j) = v.toNat := by
  have hon := hO.onw
  refine ⟨?_, fun i hi => ?_, by rw [hm, dw_write_self]⟩
  · rw [hm]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by
        rw [show O = O + BitVec.ofNat 64 0 by simp]; exact Offset.sub O (Nat.le_refl _) (by omega)⟩
    · rw [show (⟨O, 8 * (j + 1)⟩ : Region) = ⟨O + BitVec.ofNat 64 0, 8 * (j + 1)⟩ by simp]
      exact Offset.contains O (by omega) (by omega) (by omega)
  · rw [hm, dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.val i hi

/-- Word `j < 7` of the rotation. -/
theorem rotStep_ok {b O : Addr} {s0 : State} (hO : OCtx b O s0) {j : Nat} (hj : j < 7) {s : State}
    (h : RotInv b O s0 j s) : WP isa (.block (rotStep j)) s (RotInv b O s0 (j + 1)) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hO.ctx (h.gpr _ (by decide)) h.wr
  unfold rotStep
  refine WP.block_append (WP.mono (rotWord_ok hcs (j := j) (by omega)) fun s1 ⟨t0, g1, m1, rd1, wr1, sp1⟩ => ?_)
  refine rot_store hO h (by omega) g1 wr1 fun s2 u2 => WP.block_nil ?_
  have hv : (s1.gpr .t0).toNat = rw' s0.mem b j := by
    rw [t0]; show dw s.mem b _ / _ + dw s.mem b _ % _ * _ = _
    rw [own_of_rot hO (by omega) h (by omega) (by omega), own_of_rot hO (by omega) h (by omega) (by omega)]
  obtain ⟨f, v1, v2⟩ := rot_next hO (by omega) h (by rw [u2.mem, m1])
  refine ⟨fun r hr => by rw [u2.gpr, g1 r hr, h.gpr r hr], by rw [u2.rd, rd1, h.rd], by rw [u2.wr, wr1, h.wr],
    by rw [u2.sp, sp1, h.sp], f, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact v1 i hi
  · rw [v2, hv]

/-- The rotation's words 0…6, by induction. -/
theorem rotSteps_ok {b O : Addr} {s0 : State} (hO : OCtx b O s0) :
    ∀ j ≤ 7, WP isa (.block ((List.range j).flatMap rotStep)) s0 (RotInv b O s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (rotSteps_ok hO j (by omega)) fun s h => rotStep_ok hO (by omega) h)

/-- The rotation's value from its words. -/
theorem rot_val (r o : Nat → Nat) (hr : ∀ i, r i < 2 ^ 64) (h8 : r 8 < 2 ^ 9)
    (ho : ∀ i < 7, o i = r i / 2 ^ 55 + r (i + 1) % 2 ^ 55 * 2 ^ 9)
    (h7 : o 7 = r 7 / 2 ^ 55 + r 8 % 2 ^ 55 * 2 ^ 9 + r 0 % 2 ^ 46 * 2 ^ 18)
    (h8' : o 8 = r 0 / 2 ^ 46 % 2 ^ 9) :
    colsV o 9 = colsV r 9 / 2 ^ 55 + 2 ^ 466 * (colsV r 9 % 2 ^ 55) := by
  have hs := shr_cols r (s := 55) (by decide) 8
  rw [show (64 : Nat) - 55 = 9 from rfl] at hs
  have e7 : colsV o 7 = colsV (fun i => r i / 2 ^ 55 + r (i + 1) % 2 ^ 55 * 2 ^ 9) 7 := colsV_congr ho
  have hR : colsV r 9 = colsV r 8 + (2 ^ 64) ^ 8 * r 8 := rfl
  have hc8 : colsV (fun i => r i / 2 ^ 55 + r (i + 1) % 2 ^ 55 * 2 ^ 9) 8 =
      colsV (fun i => r i / 2 ^ 55 + r (i + 1) % 2 ^ 55 * 2 ^ 9) 7 +
        (2 ^ 64) ^ 7 * (r 7 / 2 ^ 55 + r 8 % 2 ^ 55 * 2 ^ 9) := rfl
  have hm : r 0 % 2 ^ 55 = r 0 % 2 ^ 46 + 2 ^ 46 * (r 0 / 2 ^ 46 % 2 ^ 9) := by
    rw [show (2 : Nat) ^ 55 = 2 ^ 46 * 2 ^ 9 by decide, Nat.mod_mul]
  have hm' := Nat.mod_lt (r 0) (show 0 < 2 ^ 55 by decide)
  have ho9 : colsV o 9 = colsV o 7 + (2 ^ 64) ^ 7 * o 7 + (2 ^ 64) ^ 8 * o 8 := rfl
  rw [Nat.mod_eq_of_lt (by omega : r 8 < 2 ^ 55)] at hs
  have h80 := hr 0
  rw [ho9, e7, h7, h8']
  rw [show (2 ^ 64) ^ 7 = (2 : Nat) ^ 448 by decide, show (2 ^ 64) ^ 8 = (2 : Nat) ^ 512 by decide] at *
  generalize colsV (fun i => r i / 2 ^ 55 + r (i + 1) % 2 ^ 55 * 2 ^ 9) 7 = C at *
  generalize colsV r 8 = R8 at *
  generalize colsV r 9 = R at *
  generalize r 0 % 2 ^ 55 = M55 at *
  generalize r 0 % 2 ^ 46 = M46 at *
  generalize r 0 / 2 ^ 46 % 2 ^ 9 = Q at *
  omega

/-- Words 7 and 8 of the rotation. -/
theorem rotTop_ok {b O : Addr} {s0 : State} (hO : OCtx b O s0) {s : State} (h : RotInv b O s0 7 s)
    (h8 : dw s0.mem b (P + 64) < 2 ^ 9) :
    WP isa (.block rotTop) s fun s' => (∀ r, r ∉ [Reg.t0, .a6] → s'.gpr r = s0.gpr r) ∧ s'.rd = s0.rd ∧
      s'.wr = s0.wr ∧ s'.sp = s0.sp ∧ Frame [⟨O, 72⟩] s0.mem s'.mem ∧
      GenWide.ov s'.mem O 9 = pw s0.mem b 0 9 / 2 ^ 55 + 2 ^ 466 * (pw s0.mem b 0 9 % 2 ^ 55) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hO.ctx (h.gpr _ (by decide)) h.wr
  have hon := hO.onw
  unfold rotTop
  refine WP.block_append (WP.mono (rotWord_ok hcs (j := 7) (by omega)) fun s1 ⟨t0, g1, m1, rd1, wr1, sp1⟩ => ?_)
  have hc1 : Ctx b s1 := ctx_of hcs (g1 _ (by decide)) wr1
  refine ld_ok hc1 (by omega) (by omega) fun s2 u2 => wp_sll (by decide) fun s3 u3 => wp_or fun s4 u4 => ?_
  have I7 : RotInv b O s0 7 s4 := ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u4.other _ hr.1, u3.other _ hr.2, u2.other _ hr.2, g1 r (by simp [hr.1, hr.2]), h.gpr r (by simp [hr.1, hr.2])],
    by rw [u4.rd, u3.rd, u2.rd, rd1, h.rd], by rw [u4.wr, u3.wr, u2.wr, wr1, h.wr],
    by rw [u4.sp, u3.sp, u2.sp, sp1, h.sp], by rw [u4.mem, u3.mem, u2.mem, m1]; exact h.frame,
    by rw [u4.mem, u3.mem, u2.mem, m1]; exact h.val⟩
  refine rot_store (j := 7) hO I7 (by omega) (fun _ _ => rfl) rfl fun s5 u5 => ?_
  obtain ⟨f5, v5, w5⟩ := rot_next hO (by omega) I7 u5.mem
  have hc5 : Ctx b s5 := ctx_of hc1 (by rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide),
    u2.other _ (by decide)]) (by rw [u5.wr, u4.wr, u3.wr, u2.wr])
  refine ld_ok hc5 (by omega) (by omega) fun s6 u6 => wp_srl (by decide) fun s7 u7 => wp_andi (by decide) fun s8 u8 => ?_
  refine wp_sd (by omega) (by rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr,
      I7.gpr _ (by decide), hO.o]) (al8 hO.oal (by omega))
    (by rw [u8.wr, u7.wr, u6.wr, u5.wr, I7.wr]; exact hO.ow 8 (by omega)) fun s9 u9 => WP.block_nil ?_
  -- The words of `r`.
  have r0 : dw s.mem b P = dw s0.mem b (P + 8 * 0) := own_of_rot hO (by omega) h (by omega) (by omega)
  have hm8 : s8.mem = s5.mem := by rw [u8.mem, u7.mem, u6.mem]
  have hm9 : s9.mem = s5.mem.writeW (O + BitVec.ofNat 64 64) (s8.gpr .t0) := by rw [u9.mem, hm8]
  have hr7 : rw' s.mem b 7 = rw' s0.mem b 7 := by
    show dw s.mem b _ / _ + dw s.mem b _ % _ * _ = _
    rw [own_of_rot hO (by omega) h (by omega) (by omega), own_of_rot hO (by omega) h (by omega) (by omega)]
  have h7lt : rw' s0.mem b 7 < 2 ^ 18 := by
    have := dw_lt s0.mem b (P + 8 * 7)
    show dw s0.mem b (P + 8 * 7) / 2 ^ 55 + dw s0.mem b (P + 8 * (7 + 1)) % 2 ^ 55 * 2 ^ 9 < _
    rw [show P + 8 * (7 + 1) = P + 64 from rfl]
    omega
  have v7 : (s4.gpr .t0).toNat = rw' s0.mem b 7 + dw s0.mem b (P + 8 * 0) % 2 ^ 46 * 2 ^ 18 := by
    rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u3.gpr, u2.gpr, or_shl18 _ _ (by rw [t0, hr7]; exact h7lt),
      t0, hr7, m1]
    show rw' s0.mem b 7 + dw s.mem b P % 2 ^ 46 * 2 ^ 18 = _
    rw [r0]
  have v8 : (s8.gpr .t0).toNat = dw s0.mem b (P + 8 * 0) / 2 ^ 46 % 2 ^ 9 := by
    rw [u8.gpr, and511, u7.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, u6.gpr]
    exact congrArg (· / 2 ^ 46 % 2 ^ 9) (own_of_frame hO (by omega) f5 (by omega) (by omega))
  refine ⟨fun r hr => by rw [u9.gpr, u8.other _ (fun e => hr (by rw [e]; decide)),
      u7.other _ (fun e => hr (by rw [e]; decide)), u6.other _ (fun e => hr (by rw [e]; decide)), u5.gpr,
      I7.gpr r hr],
    by rw [u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, I7.rd], by rw [u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, I7.wr],
    by rw [u9.sp, u8.sp, u7.sp, u6.sp, u5.sp, I7.sp], ?_, ?_⟩
  · rw [hm9]
    refine (f5.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by
        rw [show O = O + BitVec.ofNat 64 0 by simp]; exact Offset.sub O (Nat.le_refl _) (by omega)⟩
    · rw [show (⟨O, 72⟩ : Region) = ⟨O + BitVec.ofNat 64 0, 72⟩ by simp]
      exact Offset.contains O (by omega) (by omega) (by omega)
  · have hp : pw s0.mem b 0 9 = colsV (fun i => dw s0.mem b (P + 8 * i)) 9 :=
      colsV_congr fun i _ => by rw [show P + 8 * 0 + 8 * i = P + 8 * i by omega]
    rw [hp]
    refine rot_val (fun i => dw s0.mem b (P + 8 * i)) (fun i => dw s9.mem O (8 * i)) (fun _ => dw_lt _ _ _) h8
      (fun i hi => ?_) ?_ ?_
    · show dw s9.mem O (8 * i) = _
      rw [hm9, dw_write_other _ _ _ (by omega) (by omega) (by omega), v5 i hi]
    · show dw s9.mem O (8 * 7) = _
      rw [hm9, dw_write_other _ _ _ (by omega) (by omega) (by omega), w5, v7]
    · show dw s9.mem O (8 * 8) = _
      rw [hm9, dw_write_self, v8]

/-! ## The arithmetic modulo `p` -/

theorem mers_mod (u : Nat) : (u % 2 ^ 521 + u / 2 ^ 521) % (2 ^ 521 - 1) = u % (2 ^ 521 - 1) := by
  omega

/-- Rotating `r < p` right by 55 of its 521 bits divides it by `R = 2⁵⁷⁶` modulo `p`. -/
theorem rot_mod {r : Nat} (hr : r < 2 ^ 521 - 1) :
    r / 2 ^ 55 + 2 ^ 466 * (r % 2 ^ 55) < 2 ^ 521 - 1 ∧
      (r / 2 ^ 55 + 2 ^ 466 * (r % 2 ^ 55)) * 2 ^ 576 % (2 ^ 521 - 1) = r := by
  omega

/-- The correction: `(S + q) mod 2⁵²¹`, `q` the bit 521 of `S + 1`, is `S mod p`. -/
theorem canon_val {S : Nat} (hS : S < 2 ^ 521 + 2 ^ 56) :
    (S + (S + 1) / 2 ^ 521) % 2 ^ 521 < 2 ^ 521 - 1 ∧
      (S + (S + 1) / 2 ^ 521) % 2 ^ 521 = S % (2 ^ 521 - 1) := by
  by_cases h : 2 ^ 521 ≤ S + 1
  · have hq : (S + 1) / 2 ^ 521 = 1 := by omega
    rw [hq]; omega
  · have hq : (S + 1) / 2 ^ 521 = 0 := by omega
    rw [hq]; omega

theorem fold1_arith {H G X C w8 w17 : Nat} (hs : 2 ^ 9 * H + w8 % 2 ^ 9 = G + 2 ^ 576 * w17)
    (hX : X = C + 2 ^ 512 * (G + 2 ^ 576 * w17)) (hc : C < 2 ^ 512) :
    C + 2 ^ 512 * (w8 % 2 ^ 9) + H = X % 2 ^ 521 + X / 2 ^ 521 := by
  have := Nat.mod_lt w8 (show 0 < 2 ^ 9 by decide)
  omega

/-- The first fold's value: `T mod 2⁵²¹ + T >> 521`, for `T < 2¹⁰⁹⁷`. -/
theorem fold1_val (W : Nat → Nat) (hW : ∀ i, W i < 2 ^ 64) (hX : colsV W 18 < 2 ^ 1097) :
    colsV (fun i => (if i < 8 then W i else W i % 2 ^ 9) + (W (8 + i) / 2 ^ 9 + W (9 + i) % 2 ^ 9 * 2 ^ 55)) 9 =
      colsV W 18 % 2 ^ 521 + colsV W 18 / 2 ^ 521 := by
  rw [colsV_add']
  have hl : colsV (fun i => if i < 8 then W i else W i % 2 ^ 9) 9 = colsV W 8 + (2 ^ 64) ^ 8 * (W 8 % 2 ^ 9) := by
    show colsV (fun i => if i < 8 then W i else W i % 2 ^ 9) 8 + _ = _
    rw [colsV_congr (g := W) fun i hi => ite_eq_left hi]; rfl
  have hs := shr_cols (fun i => W (8 + i)) (s := 9) (by decide) 9
  rw [show (64 : Nat) - 9 = 55 from rfl] at hs
  have hh : colsV (fun i => W (8 + i) / 2 ^ 9 + W (8 + (i + 1)) % 2 ^ 9 * 2 ^ 55) 9 =
      colsV (fun i => W (8 + i) / 2 ^ 9 + W (9 + i) % 2 ^ 9 * 2 ^ 55) 9 :=
    colsV_congr fun i _ => by rw [show 8 + (i + 1) = 9 + i by omega]
  rw [hh] at hs
  have hsp := colsV_split W 8 10
  have h10 : colsV (fun j => W (8 + j)) 10 = colsV (fun j => W (8 + j)) 9 + (2 ^ 64) ^ 9 * W (8 + 9) := rfl
  have h17 : colsV W 18 = colsV W 17 + (2 ^ 64) ^ 17 * W 17 := rfl
  have hc8 := GenWide.colsV_lt W hW 8
  have e8 : ((2 : Nat) ^ 64) ^ 8 = 2 ^ 512 := by rw [← Nat.pow_mul]
  have e9 : ((2 : Nat) ^ 64) ^ 9 = 2 ^ 576 := by rw [← Nat.pow_mul]
  have e17 : ((2 : Nat) ^ 64) ^ 17 = 2 ^ 1088 := by rw [← Nat.pow_mul]
  rw [e8] at hl hsp hc8
  rw [e9] at hs h10
  rw [e17] at h17
  rw [hl]
  have hw17 : W 17 < 2 ^ 9 := by
    rcases Nat.lt_or_ge (W 17) (2 ^ 9) with h | h
    · exact h
    · exfalso
      have : 2 ^ 1088 * 2 ^ 9 ≤ 2 ^ 1088 * W 17 := Nat.mul_le_mul_left _ h
      omega
  rw [show 8 + 9 = 17 from rfl] at h10 hs
  rw [Nat.mod_eq_of_lt hw17] at hs
  rw [show 8 + 0 = 8 from rfl] at hs
  have hX' : colsV W 18 = colsV W 8 + 2 ^ 512 * (colsV (fun j => W (8 + j)) 9 + 2 ^ 576 * W 17) := by
    rw [← h10]; exact hsp
  exact fold1_arith hs hX' hc8

theorem fold2_arith {L8 w8 c c' R S : Nat} (hS : S = L8 + 2 ^ 512 * w8 + 2 ^ 576 * c) (hL : L8 < 2 ^ 512)
    (hSlt : S < 2 ^ 521 + 2 ^ 576) (hR : R < 2 ^ 576)
    (v5 : R + 2 ^ 576 * c' = L8 + 2 ^ 512 * (w8 % 2 ^ 9) + (w8 / 2 ^ 9 + c * 2 ^ 55)) :
    R = S % 2 ^ 521 + S / 2 ^ 521 ∧ R < 2 ^ 521 + 2 ^ 56 := by
  have h1 : S % 2 ^ 521 = L8 + 2 ^ 512 * (w8 % 2 ^ 9) := by omega
  have h2 : S / 2 ^ 521 = w8 / 2 ^ 9 + c * 2 ^ 55 := by omega
  have h3 : S / 2 ^ 521 ≤ 2 ^ 55 := by omega
  have h4 : c' = 0 := by omega
  subst h4
  omega

/-! ## The multiplication -/

open VG.Proof.Weierstrass.RISCV64.GenWide (CoreOk ownR clobW xv ov) in
theorem notin {r : Reg} (hr : r ∉ clobW) {L : List Reg} (hL : ∀ x ∈ L, x ∈ clobW := by decide) : r ∉ L :=
  fun h => hr (hL r h)

section
open VG.Proof.Weierstrass.RISCV64.GenWide (CoreOk ownR clobW xv ov)

/-- The reduction of the product `T` into `[O]`: the folds, the correction and the rotation. -/
theorem tail_ok {b A B O : Addr} {s s3 : State} (hC : CoreOk 9 b A B O s) (hB : xv s.mem B 9 < 2 ^ 521 - 1)
    (h3 : ProdOk b A B s s3) :
    WP isa (.block tail) s3 fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownR 9 b, ⟨O, 8 * 9⟩] s.mem s'.mem ∧
      ov s'.mem O 9 < 2 ^ 521 - 1 ∧ ov s'.mem O 9 * 2 ^ 576 % (2 ^ 521 - 1) = xv s.mem A 9 * xv s.mem B 9 % (2 ^ 521 - 1) := by
  have hP := P_eq
  have hT : T 9 = 1472 := rfl
  have hb := hC.nowrap
  have hal := hC.ctx.al
  unfold tail
  simp only [List.append_assoc]
  have hc3 : Ctx b s3 := ctx_of hC.ctx (h3.gpr _ (by decide)) h3.wr
  have v3 := h3.val
  have hXlt : xv s.mem A 9 * xv s.mem B 9 < 2 ^ 1097 := by
    have hA : xv s.mem A 9 < ((2 : Nat) ^ 64) ^ 9 := GenWide.colsV_lt (fun j => dw s.mem A (8 * j)) (fun _ => dw_lt _ _ _) 9
    rw [show ((2 : Nat) ^ 64) ^ 9 = 2 ^ 576 by rw [← Nat.pow_mul]] at hA
    calc xv s.mem A 9 * xv s.mem B 9 ≤ (2 ^ 576 - 1) * (2 ^ 521 - 1) :=
          Nat.mul_le_mul (Nat.le_sub_one_of_lt hA) (Nat.le_of_lt hB)
      _ < 2 ^ 1097 := by decide
  generalize hX : xv s.mem A 9 * xv s.mem B 9 = X at v3 hXlt
  -- The first fold.
  refine WP.block_append (WP.mono (fold_ok hc3) fun s4 ⟨g4, rd4, wr4, sp4, f4, c4, v4⟩ => ?_)
  have hc4 : Ctx b s4 := ctx_of hc3 (g4 _ (by decide)) wr4
  have hW : pw s3.mem b 0 18 = colsV (fun i => dw s3.mem b (P + 8 * i)) 18 :=
    colsV_congr fun i _ => by rw [show P + 8 * 0 + 8 * i = P + 8 * i by omega]
  rw [hW] at v3
  have e4 := fold1_val (fun i => dw s3.mem b (P + 8 * i)) (fun _ => dw_lt _ _ _) (by rw [v3]; exact hXlt)
  rw [v3] at e4
  rw [show colsV (fun i => lw s3.mem b i + hw s3.mem b i) 9 = colsV (fun i => (if i < 8 then dw s3.mem b (P + 8 * i)
      else dw s3.mem b (P + 8 * i) % 2 ^ 9) + (dw s3.mem b (P + 8 * (8 + i)) / 2 ^ 9 +
        dw s3.mem b (P + 8 * (9 + i)) % 2 ^ 9 * 2 ^ 55)) 9 from rfl, e4] at v4
  -- The second fold.
  refine WP.block_append (WP.mono (fold2_ok hc4 c4) fun s5 ⟨g5, rd5, wr5, sp5, f5, v5⟩ => ?_)
  have hc5 : Ctx b s5 := ctx_of hc4 (g5 _ (by decide)) wr5
  have h48 : pw s4.mem b 0 9 = pw s4.mem b 0 8 + 2 ^ 512 * dw s4.mem b (P + 64) := by
    rw [pw_succ, show ((2 : Nat) ^ 64) ^ 8 = 2 ^ 512 by rw [← Nat.pow_mul]]
  have l48 := pw_lt s4.mem b 8
  rw [show ((2 : Nat) ^ 64) ^ 8 = 2 ^ 512 by rw [← Nat.pow_mul]] at l48
  have l59 := pw_lt s5.mem b 9
  rw [show ((2 : Nat) ^ 64) ^ 9 = 2 ^ 576 by rw [← Nat.pow_mul]] at l59
  generalize hS : X % 2 ^ 521 + X / 2 ^ 521 = S at v4
  have hSlt : S < 2 ^ 521 + 2 ^ 576 := by omega
  have hS2 : pw s5.mem b 0 9 = S % 2 ^ 521 + S / 2 ^ 521 ∧ pw s5.mem b 0 9 < 2 ^ 521 + 2 ^ 56 :=
    fold2_arith (by rw [← v4, h48]) l48 hSlt l59 v5
  -- The correction.
  refine WP.block_append (WP.mono (canon_ok hc5 hS2.2) fun s6 ⟨g6, rd6, wr6, sp6, f6, v6⟩ => ?_)
  have hc6 : Ctx b s6 := ctx_of hc5 (g6 _ (by decide)) wr6
  obtain ⟨rlt, req⟩ := canon_val hS2.2
  rw [← v6] at rlt req
  -- The rotation.
  have hO : OCtx b O s6 :=
    ⟨hc6, hb, by rw [g6 _ (by decide), g5 _ (by decide), g4 _ (by decide), h3.gpr _ (by decide), hC.o],
      hC.oal, by rw [wr6, wr5, wr4, h3.wr]; exact hC.ow, hC.onw, hC.odis⟩
  have h68 : dw s6.mem b (P + 64) < 2 ^ 9 := by
    have e : pw s6.mem b 0 9 = pw s6.mem b 0 8 + (2 ^ 64) ^ 8 * dw s6.mem b (P + 8 * 8) := pw_succ s6.mem b 8
    rw [show ((2 : Nat) ^ 64) ^ 8 = 2 ^ 512 by rw [← Nat.pow_mul]] at e
    rw [show P + 8 * 8 = P + 64 from rfl] at e
    omega
  refine WP.block_append (WP.mono (rotSteps_ok hO 7 (Nat.le_refl _)) fun s7 h7 => ?_)
  refine WP.mono (rotTop_ok hO h7 h68) fun s8 ⟨g8, rd8, wr8, sp8, f8, v8⟩ => ?_
  obtain ⟨olt, oeq⟩ := rot_mod rlt
  rw [← v8] at olt oeq
  have hO6 : ∀ x ∈ [Region.mk (b + BitVec.ofNat 64 P) 72], ∃ r' ∈ [ownR 9 b, ⟨O, 8 * 9⟩], Region.Sub x r' :=
    fun x hx => by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_self .., own_sub (Nat.le_refl _) (by omega)⟩
  refine ⟨fun r hr => ?_, by rw [rd8, rd6, rd5, rd4, h3.rd], by rw [wr8, wr6, wr5, wr4, h3.wr],
    by rw [sp8, sp6, sp5, sp4, h3.sp], ?_, olt, ?_⟩
  · rw [g8 r (notin hr), g6 r (notin hr), g5 r (notin hr), g4 r (notin hr), h3.gpr r hr]
  · have F2 : Frame [ownR 9 b, ⟨O, 8 * 9⟩] s.mem s3.mem := h3.frame.sub fun x hx => by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_self .., own_sub (Nat.le_refl _) (by omega)⟩
    have F8 : Frame [ownR 9 b, ⟨O, 8 * 9⟩] s6.mem s8.mem := f8.sub fun x hx => by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    exact (((F2.trans (f4.sub hO6)).trans (f5.sub hO6)).trans (f6.sub hO6)).trans F8
  · rw [oeq, req, hS2.1, mers_mod, ← hS, mers_mod]

/-- `mulCore`: `[o] R ≡ [a] [b]` modulo `p`, `[o] < p`. -/
theorem mulCore_ok {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) (hB : xv s.mem B 9 < 2 ^ 521 - 1) :
    WP isa (.block mulCore) s fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownR 9 b, ⟨O, 8 * 9⟩] s.mem s'.mem ∧
      ov s'.mem O 9 < 2 ^ 521 - 1 ∧ ov s'.mem O 9 * 2 ^ 576 % (2 ^ 521 - 1) = xv s.mem A 9 * xv s.mem B 9 % (2 ^ 521 - 1) := by
  unfold mulCore
  have hPC : PCtx b A B s :=
    ⟨hC.ctx, hC.nowrap, hC.a, hC.b', hC.aal, hC.bal, hC.ain, hC.bin, hC.adis, hC.bdis⟩
  exact WP.block_append (WP.mono (productC_ok hPC) fun s3 h3 => tail_ok hC hB h3)

/-- `sqCore`: `[o] R ≡ [a]²` modulo `p`, `[o] < p`. -/
theorem sqCore_ok {b A O : Addr} {s : State} (hC : CoreOk 9 b A A O s) (hB : xv s.mem A 9 < 2 ^ 521 - 1) :
    WP isa (.block sqCore) s fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownR 9 b, ⟨O, 8 * 9⟩] s.mem s'.mem ∧
      ov s'.mem O 9 < 2 ^ 521 - 1 ∧ ov s'.mem O 9 * 2 ^ 576 % (2 ^ 521 - 1) = xv s.mem A 9 * xv s.mem A 9 % (2 ^ 521 - 1) := by
  unfold sqCore
  have hPC : PCtx b A A s :=
    ⟨hC.ctx, hC.nowrap, hC.a, hC.b', hC.aal, hC.bal, hC.ain, hC.bin, hC.adis, hC.bdis⟩
  exact WP.block_append (WP.mono (squareC_ok hPC) fun s3 h3 => tail_ok hC hB h3)

open VG.Proof.Weierstrass.RISCV64.GenWide (CoreSpec) in
/-- `mulCore`, on the byte-wise copies. -/
theorem mulCore_spec :
    CoreSpec 9 mulCore (fun _ B => B < 2 ^ 521 - 1)
      (fun A B r => r < 2 ^ 521 - 1 ∧ r * 2 ^ (64 * 9) % (2 ^ 521 - 1) = A * B % (2 ^ 521 - 1)) :=
  fun hC hB => WP.mono (mulCore_ok hC hB) fun _ ⟨g, rd, wr, sp, f, v1, v2⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

open VG.Proof.Weierstrass.RISCV64.GenWide (FastSpec ownR_sub) in
/-- `core`: the square if the pointers are equal, else the product. -/
theorem core_spec :
    FastSpec 9 core (fun _ B => B < 2 ^ 521 - 1)
      (fun A B r => r < 2 ^ 521 - 1 ∧ r * 2 ^ (64 * 9) % (2 ^ 521 - 1) = A * B % (2 ^ 521 - 1)) := by
  intro b A B O s hC _ _ _ hB
  refine WP.mono (Q := fun (s' : State) => _ ∧ Frame [ownR 9 b, ⟨O, 8 * 9⟩] s.mem s'.mem ∧ _) ?_
    fun _ ⟨v, f, r⟩ => ⟨v, f.sub (ownR_sub 9 (by decide) _), r⟩
  unfold core
  refine WP.ite (s.gpr .t4 == s.gpr .t5) rfl (fun he => ?_) (fun _ => ?_)
  · have hAB : A = B := by rw [← hC.a, ← hC.b']; exact beq_iff_eq.mp he
    subst hAB
    exact WP.mono (sqCore_ok hC hB) fun _ ⟨g, rd, wr, sp, f, v1, v2⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩
  · exact WP.mono (mulCore_ok hC hB) fun _ ⟨g, rd, wr, sp, f, v1, v2⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

end

open VG.Impl.Weierstrass.Mont (p521p) in
open VG.Proof.Weierstrass.RISCV64 (mulRV) in
open VG.Proof.Weierstrass.RISCV64.GenWide (fnWith_rv) in
/-- `vg_p521_mul_mod_p` by its Mersenne form meets the contract by register. -/
theorem mul_rv (s : State) (hs : (mulRV p521p).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p521p).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnWith_rv (S := p521p) (by decide) (by decide) @core_spec @mulCore_spec hs.1
    hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

open VG.Impl.Weierstrass.Mont (p521p) in
open VG.Proof.Weierstrass.RISCV64 (mulRV alignedC) in
open VG.Proof.Weierstrass.RISCV64.GenWide (fnA_rv) in
/-- `vg_p521_mul_mod_p` for aligned offsets meets the contract by register for them. -/
theorem mulA_rv (s : State) (hs : (alignedC (mulRV p521p)).pre s) :
    ∃ t s', Exec isa mulFnA s t s' ∧ abiPreserved s s' ∧ (mulRV p521p).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnA_rv (S := p521p) (by decide) (by decide) @core_spec hs.1.1 hs.2
    (by exact hs.1.2)
  exact ⟨t, s', he, a, v1, v2, k⟩

end VG.Proof.Weierstrass.RISCV64.P521Mersenne
