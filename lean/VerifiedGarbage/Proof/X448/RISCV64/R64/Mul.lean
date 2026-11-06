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

* `pipe x y ts` (`pipe_ok`), for a table of terms `ts` (`Tab`): each term's
  sums into the column's accumulator, with the next term's product and the
  one after's operands, which the pipeline (`Pipe`) carries from term to
  term (`pstep_ok`), the terms of a column (`pterms_ok`) and the columns
  (`columns_ok`) by induction.
* `product x y` (`product_ok`): `pipe` of every term; the columns sum to the
  product (`mulCols_sum`).
* `square x` (`square_ok`): `pipe` of the cross products `a_j a_i`
  (`j < i`, `sqPairs`); then
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

/-- The columns of a product: column `k` is the sum of `a_i b_j` with `i + j = k`. -/
def mulF (X Y : Nat → Nat) (p : Nat × Nat) : Nat := X p.1 * Y p.2

def mulCs (X Y : Nat → Nat) (k : Nat) : Nat := tsum (mulF X Y) (colPairs k)

/-- A cross term's value: `a_j a_i` for the term `(i, j)`. -/
def sqF (X : Nat → Nat) (p : Nat × Nat) : Nat := X p.2 * X p.1

/-- The columns of the cross products. -/
def sqCs (X : Nat → Nat) (k : Nat) : Nat := tsum (sqF X) (sqPairs k)

theorem sqCs_eq (X : Nat → Nat) : sqCs X = fun k => tsum (mulF X X) (sqPairs k) := by
  funext k; unfold sqCs tsum; congr 1; exact List.map_congr_left fun p _ => Nat.mul_comm _ _

section
variable {b : Addr}

/-- The element at `x`, unchanged in a frame of `ACC`. -/
theorem dw_acc {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] m m') {d : Nat}
    (hd : d + 8 ≤ ACC) : dw m' b d = dw m b d :=
  dw_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := ACC_eq
    exact Offset.disjoint _ (.inl hd) (by omega) (by omega)

theorem mulF_le (X Y : Nat → Nat) (hX : ∀ i, X i < 2 ^ 64) (hY : ∀ j, Y j < 2 ^ 64) (p : Nat × Nat) :
    mulF X Y p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := hX p.1; omega) (by have := hY p.2; omega)

theorem tsum_mul_lt {X Y : Nat → Nat} (hX : ∀ i, X i < 2 ^ 64) (hY : ∀ j, Y j < 2 ^ 64)
    {ps : List (Nat × Nat)} (hl : ps.length ≤ 7) : tsum (mulF X Y) ps < 7 * 2 ^ 128 := by
  have := tsum_le (ps := ps) fun p _ => mulF_le X Y hX hY p
  have : ps.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) ≤ 7 * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) :=
    Nat.mul_le_mul_right _ hl
  omega

/-! ### The pipeline -/

theorem PR_mod (n : Nat) : PR (n % 2) = PR n := by
  simp only [PR, Nat.mod_mod]

theorem PR_mod1 (n : Nat) : PR (n % 2 + 1) = PR (n + 1) := by
  simp only [PR]; rw [show (n % 2 + 1) % 2 = (n + 1) % 2 by omega]

/-- The registers of a step's products, by the parity of the term. -/
theorem regs_pr : ∀ e < 2,
    (PR e).1 ≠ (PR e).2 ∧ (PR e).1 ≠ .a1 ∧ (PR e).1 ≠ .a2 ∧ (PR e).2 ≠ .a1 ∧ (PR e).2 ≠ .a2 ∧
    (PR e).1 ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧ (PR e).2 ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧
    (PR (e + 1)).1 ∉ [Reg.a1, .a2] ∧ (PR (e + 1)).2 ∉ [Reg.a1, .a2] ∧
    (PR e).1 ∈ clob64 ∧ (PR e).2 ∈ clob64 := by decide

/-- The accumulator's register `rr k` apart from a step's others. -/
theorem regs_acc : ∀ k < 17, ∀ e < 2,
    rr k ≠ (PR e).1 ∧ rr k ≠ (PR e).2 ∧ rr k ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧ rr k ∉ [Reg.a1, .a2] := by
  decide

/-- The registers a step's sums write, apart from the next product's and the operands. -/
theorem regs_sum : ∀ k < 14, ∀ e < 2,
    (PR (e + 1)).1 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] ∧
    (PR (e + 1)).2 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] ∧
    Reg.a1 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] ∧
    Reg.a2 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] := by decide

theorem pstart_succ (cs : Nat → Nat) (k : Nat) : pstart cs (k + 1) = pstart cs k + cs k := by
  simp [pstart, List.range_succ]

/-- What the code of a table of terms `ts` needs: its terms are column `k`'s
pairs `ps k` in order, from `pstart` on, with words below 7. -/
structure Tab (ts : List (Nat × Nat × Nat)) (ps : Nat → List (Nat × Nat)) : Prop where
  take : ∀ k < 14, ∀ m < (ps k).length,
    (ps k).take (m + 1) = (ps k).take m ++ [(tm ts (pstart (fun c => (ps c).length) k + m)).2]
  le : ∀ k < 14, pstart (fun c => (ps c).length) k + (ps k).length ≤ ts.length
  lt : ∀ n < ts.length, (tm ts n).2.1 < 7 ∧ (tm ts n).2.2 < 7
  len : ∀ k < 14, (ps k).length ≤ 7
  all : pstart (fun c => (ps c).length) 14 = ts.length

theorem tab_mul : Tab (terms colPairs) colPairs :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem tab_sq : Tab (terms sqPairs) sqPairs :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The pipeline at term `n`: its product in `PR n`, the next term's operands in `a1` and `a2`. -/
structure Pipe (X Y : Nat → Nat) (ts : List (Nat × Nat × Nat)) (n : Nat) (s : State) : Prop where
  prod : n < ts.length →
    (s.gpr (PR n).1).toNat + 2 ^ 64 * (s.gpr (PR n).2).toNat = X (tm ts n).2.1 * Y (tm ts n).2.2
  ops : n + 1 < ts.length →
    (s.gpr .a1).toNat = X (tm ts (n + 1)).2.1 ∧ (s.gpr .a2).toNat = Y (tm ts (n + 1)).2.2

theorem Pipe.of {X Y : Nat → Nat} {ts : List (Nat × Nat × Nat)} {n : Nat} {s s' : State} (h : Pipe X Y ts n s)
    (e1 : s'.gpr (PR n).1 = s.gpr (PR n).1) (e2 : s'.gpr (PR n).2 = s.gpr (PR n).2)
    (e3 : s'.gpr .a1 = s.gpr .a1) (e4 : s'.gpr .a2 = s.gpr .a2) : Pipe X Y ts n s' :=
  ⟨fun hn => by rw [e1, e2]; exact h.prod hn, fun hn => by rw [e3, e4]; exact h.ops hn⟩

/-- Term `n`'s product, if it is one. -/
theorem mulN_ok (ts : List (Nat × Nat × Nat)) (n : Nat) {s : State} :
    WP isa (.block (mulN ts n)) s fun s' =>
      (n < ts.length →
        (s'.gpr (PR n).1).toNat + 2 ^ 64 * (s'.gpr (PR n).2).toNat = (s.gpr .a1).toNat * (s.gpr .a2).toNat) ∧
      Keeps [(PR n).1, (PR n).2] s s' := by
  unfold mulN
  split
  · obtain ⟨p12, p1a1, p1a2, -⟩ := regs_pr _ (Nat.mod_lt n (by decide))
    rw [PR_mod] at p12 p1a1 p1a2
    exact WP.mono (mulWide_ok p1a1 p1a2 p12) fun _ ⟨e, k⟩ => ⟨fun _ => e, k⟩
  · exact WP.block_nil ⟨fun h => absurd h ‹_›, Keeps.refl _ _⟩

/-- Term `n`'s operands, if it is one. -/
theorem ldN_ok {s0 : State} {x y : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) (hy : y + 56 ≤ ACC)
    (hy8 : y % 8 = 0) {ts : List (Nat × Nat × Nat)} (hlt : ∀ n < ts.length, (tm ts n).2.1 < 7 ∧ (tm ts n).2.2 < 7)
    (n : Nat) {s : State} (hc : Ctx b s) (hf : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem) :
    WP isa (.block (ldN x y ts n)) s fun s' => Keeps [.a1, .a2] s s' ∧
      (n < ts.length → (s'.gpr .a1).toNat = dw s0.mem b (x + 8 * (tm ts n).2.1) ∧
        (s'.gpr .a2).toNat = dw s0.mem b (y + 8 * (tm ts n).2.2)) := by
  have hA := ACC_eq
  unfold ldN
  split
  · rename_i hn
    obtain ⟨hi, hj⟩ := hlt n hn
    refine ld_ok hc (by omega) (by omega) fun s1 u1 => ?_
    refine ld_ok (hc.of_rest (u1.rest (ws := [.a1]) (by simp)) (by decide)) (by omega) (by omega) fun s2 u2 =>
      WP.block_nil ?_
    refine ⟨⟨fun r hr => ?_, by rw [u2.mem, u1.mem], by rw [u2.rd, u1.rd], by rw [u2.wr, u1.wr],
      by rw [u2.sp, u1.sp]⟩, fun _ => ⟨?_, ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u2.other _ hr.2, u1.other _ hr.1]
    · rw [u2.other _ (by decide), u1.gpr]; exact dw_acc hf (by omega)
    · rw [u2.gpr, u1.mem]; exact dw_acc hf (by omega)
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

/-- Term `n` of column `k`: the next product and operands, then this one's sums. -/
theorem pstep_ok {s0 : State} {x y : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) (hy : y + 56 ≤ ACC)
    (hy8 : y % 8 = 0) {ts : List (Nat × Nat × Nat)} (hlt : ∀ n < ts.length, (tm ts n).2.1 < 7 ∧ (tm ts n).2.2 < 7)
    {k n : Nat} (hk : k < 14) (hn : n < ts.length) {s : State} (hc : Ctx b s) (hr : Rest clob64 s0 s)
    (hf : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem)
    (hp : Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts n s)
    (hb : val3 s (rr k) (rr (k + 1)) (rr (k + 2)) +
      dw s0.mem b (x + 8 * (tm ts n).2.1) * dw s0.mem b (y + 8 * (tm ts n).2.2) < 2 ^ 192) :
    WP isa (.block (pstep x y ts k n)) s fun s' => Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s'.mem ∧ s'.mem = s.mem ∧
      Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts (n + 1) s' ∧
      val3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) +
        dw s0.mem b (x + 8 * (tm ts n).2.1) * dw s0.mem b (y + 8 * (tm ts n).2.2) := by
  obtain ⟨h01, h02, h12, -⟩ := rr_ne k hk
  have he : n % 2 < 2 := Nat.mod_lt _ (by decide)
  have h1 := regs_pr _ he
  have h2 := regs_acc k (by omega) _ he
  have h3 := regs_acc (k + 1) (by omega) _ he
  have h4 := regs_acc (k + 2) (by omega) _ he
  have h5 := regs_sum k hk _ he
  have h6 := regs_pr _ (Nat.mod_lt (n + 1) (by decide))
  rw [PR_mod, PR_mod1] at h1 h2 h3 h4 h5
  rw [PR_mod] at h6
  obtain ⟨p12, p1a1, p1a2, p2a1, p2a2, p1n, p2n, q1a, q2a, pc1, pc2⟩ := h1
  obtain ⟨a1p, a2p, z0n, z0a⟩ := h2
  obtain ⟨b1p, b2p, z1n, z1a⟩ := h3
  obtain ⟨c1p, c2p, z2n, z2a⟩ := h4
  obtain ⟨q1n, q2n, a1n, a2n⟩ := h5
  obtain ⟨-, -, -, -, -, -, -, -, -, qc1, qc2⟩ := h6
  have kr : ∀ {rs : List Reg} {s s' : State}, Keeps rs s s' → (∀ r ∈ rs, r ∈ clob64) → Rest clob64 s s' :=
    fun k hs => (Keeps.rest k).mono hs
  unfold pstep
  rw [List.append_assoc]
  refine WP.append (mulN_ok ts (n + 1)) fun s1 ⟨e1, k1⟩ => ?_
  have r1 := kr k1 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  have hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  have hf1 : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s1.mem := by rw [k1.2.1]; exact hf
  refine WP.append (ldN_ok hx hx8 hy hy8 hlt (n + 2) hc1 hf1) fun s2 ⟨k2, e2⟩ => ?_
  have r2 := kr k2 (by decide)
  have g1 : ∀ r, r ∉ [(PR (n + 1)).1, (PR (n + 1)).2] → r ∉ [Reg.a1, .a2] → s2.gpr r = s.gpr r :=
    fun r h1 h2 => (k2.1 r h2).trans (k1.1 r h1)
  have pp := hp.prod hn
  rw [← g1 _ p1n (by simp [p1a1, p1a2]), ← g1 _ p2n (by simp [p2a1, p2a2])] at pp
  have hv2 : val3 s2 (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) := by
    simp only [val3]
    rw [g1 _ z0n z0a, g1 _ z1n z1a, g1 _ z2n z2a]
  have hX := dw_lt s0.mem b (x + 8 * (tm ts n).2.1)
  have hY := dw_lt s0.mem b (y + 8 * (tm ts n).2.2)
  have hXY : dw s0.mem b (x + 8 * (tm ts n).2.1) * dw s0.mem b (y + 8 * (tm ts n).2.2) ≤
      (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hq : (s2.gpr (PR n).2).toNat < 2 ^ 64 - 1 := by
    have := (s2.gpr (PR n).1).isLt
    omega
  refine WP.mono (accG_ok h01 h02 h12 a1p a2p b1p b2p c1p c2p p12) fun s3 ⟨e3, k3⟩ => ?_
  have r3 := kr k3 (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> first | exact rr_clob _ | with_reducible assumption)
  have r13 := r1.trans (r2.trans r3)
  refine ⟨hc.of_rest r13 (by decide), hr.trans r13, by rw [k3.2.1, k2.2.1, k1.2.1]; exact hf,
    by rw [k3.2.1, k2.2.1, k1.2.1], ⟨fun hn1 => ?_, fun hn2 => ?_⟩, ?_⟩
  · rw [k3.1 _ q1n, k3.1 _ q2n, k2.1 _ q1a, k2.1 _ q2a, (e1 hn1)]
    obtain ⟨o1, o2⟩ := hp.ops hn1
    rw [o1, o2]
  · rw [k3.1 _ a1n, k3.1 _ a2n]
    exact e2 hn2
  · rw [e3 hq, hv2, pp, Nat.mod_eq_of_lt hb]

theorem tsum_snoc (f : Nat × Nat → Nat) (ps : List (Nat × Nat)) (p : Nat × Nat) :
    tsum f (ps ++ [p]) = tsum f ps + f p := by simp [tsum]

/-- Column `k`'s first `m` terms, by induction on them. -/
theorem pterms_ok {s0 : State} {x y : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) (hy : y + 56 ≤ ACC)
    (hy8 : y % 8 = 0) {ts : List (Nat × Nat × Nat)} {ps : Nat → List (Nat × Nat)} (ht : Tab ts ps)
    {k : Nat} (hk : k < 14) :
    ∀ m ≤ (ps k).length, ∀ s, Ctx b s → Rest clob64 s0 s → Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem →
      Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts
        (pstart (fun c => (ps c).length) k) s →
      val3 s (rr k) (rr (k + 1)) (rr (k + 2)) < 2 ^ 128 →
      WP isa (.block ((List.range' (pstart (fun c => (ps c).length) k) m).flatMap (pstep x y ts k))) s fun s' =>
        Ctx b s' ∧ Rest clob64 s0 s' ∧ Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s'.mem ∧ s'.mem = s.mem ∧
        Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts
          (pstart (fun c => (ps c).length) k + m) s' ∧
        val3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) +
          tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j))) ((ps k).take m)
  | 0, _, s, hc, hr, hf, hp, _ => WP.block_nil ⟨hc, hr, hf, rfl, hp, by simp [tsum]⟩
  | m + 1, hm, s, hc, hr, hf, hp, hv => by
    rw [List.range'_concat, Nat.one_mul, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (pterms_ok hx hx8 hy hy8 ht hk m (by omega) s hc hr hf hp hv)
      fun s1 ⟨hc1, hr1, hf1, m1, hp1, hv1⟩ => ?_
    have hX : ∀ i, dw s0.mem b (x + 8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
    have hY : ∀ j, dw s0.mem b (y + 8 * j) < 2 ^ 64 := fun j => dw_lt _ _ _
    have hts := tsum_mul_lt hX hY (ps := (ps k).take m)
      (by rw [List.length_take]; exact Nat.le_trans (Nat.min_le_right _ _) (ht.len k hk))
    have hxy : dw s0.mem b (x + 8 * (tm ts (pstart (fun c => (ps c).length) k + m)).2.1) *
        dw s0.mem b (y + 8 * (tm ts (pstart (fun c => (ps c).length) k + m)).2.2) < 2 ^ 128 :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (hX _) (hY _)) (by decide)
    refine WP.mono (pstep_ok hx hx8 hy hy8 ht.lt hk (by have := ht.le k hk; omega) hc1 hr1 hf1 hp1
      (by rw [hv1]; omega)) fun s2 ⟨hc2, hr2, hf2, m2, hp2, hv2⟩ =>
        ⟨hc2, hr2, hf2, m2.trans m1, by rw [← Nat.add_assoc]; exact hp2, ?_⟩
    rw [hv2, hv1, ht.take k hk m (by omega), tsum_snoc]
    simp only [mulF]; omega

/-- Column `k`: its terms, then its end. -/
theorem pcol_ok {s0 : State} {x y : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) (hy : y + 56 ≤ ACC)
    (hy8 : y % 8 = 0) {ts : List (Nat × Nat × Nat)} {ps : Nat → List (Nat × Nat)} (ht : Tab ts ps)
    {k : Nat} (hk : k < 14) {s : State}
    (h : ColInv b s0 (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)))
      (ps c)) k s)
    (hp : Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts
      (pstart (fun c => (ps c).length) k) s) :
    WP isa (.block (pcol x y ts (fun c => (ps c).length) k)) s fun s' =>
      ColInv b s0 (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)))
        (ps c)) (k + 1) s' ∧
      Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts
        (pstart (fun c => (ps c).length) (k + 1)) s' := by
  have hv0 : val3 s (rr k) (rr (k + 1)) (rr (k + 2)) =
      (s.gpr (rr k)).toNat + 2 ^ 64 * (s.gpr (rr (k + 1))).toNat := by
    simp only [val3, h.top]; rfl
  have hl := (s.gpr (rr k)).isLt
  have hh := (s.gpr (rr (k + 1))).isLt
  have hX : ∀ i, dw s0.mem b (x + 8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
  have hY : ∀ j, dw s0.mem b (y + 8 * j) < 2 ^ 64 := fun j => dw_lt _ _ _
  have hbd := tsum_mul_lt hX hY (ht.len k hk)
  obtain ⟨x1, x2, -, z0a⟩ := regs_acc k (by omega) _ (Nat.mod_lt (pstart (fun c => (ps c).length) (k + 1)) (by decide))
  rw [PR_mod] at x1 x2
  unfold pcol
  refine WP.append (pterms_ok hx hx8 hy hy8 ht hk _ (Nat.le_refl _) s h.ctx h.rest h.frame hp
    (by rw [hv0]; omega_arith)) fun s1 ⟨hc1, hr1, hf1, m1, hp1, hv1⟩ => ?_
  rw [List.take_length] at hv1
  rw [← pstart_succ] at hp1
  have hwp := colEnd_ok (cs := fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i))
    (fun j => dw s0.mem b (y + 8 * j))) (ps c)) hk hc1 hr1 hf1 (by
      rw [show accW s1.mem b k = accW s.mem b k by rw [m1], hv1, hv0, colsV, ← h.val, Nat.mul_add]; omega_arith)
  exact WP.mono hwp fun s2 ⟨h2, g2⟩ => ⟨h2, hp1.of (g2 _ (Ne.symm x1)) (g2 _ (Ne.symm x2))
    (g2 _ fun e => z0a (by rw [← e]; simp)) (g2 _ fun e => z0a (by rw [← e]; simp))⟩

/-- `pipe x y ts`: the columns of the terms `ts` at `ACC`. -/
theorem pipe_ok {s0 : State} {x y : Nat} (hx : x + 56 ≤ ACC) (hx8 : x % 8 = 0) (hy : y + 56 ≤ ACC)
    (hy8 : y % 8 = 0) {ts : List (Nat × Nat × Nat)} {ps : Nat → List (Nat × Nat)} (ht : Tab ts ps)
    (hc : Ctx b s0) :
    WP isa (.block (pipe x y ts fun c => (ps c).length)) s0
      (ColInv b s0 (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)))
        (ps c)) 14) := by
  have kr : ∀ {rs : List Reg} {s s' : State}, Keeps rs s s' → (∀ r ∈ rs, r ∈ clob64) → Rest clob64 s s' :=
    fun k hs => (Keeps.rest k).mono hs
  unfold pipe
  simp only [List.append_assoc]
  refine WP.append zero3_ok fun s1 ⟨e4, e5, e6, hr1, hm1⟩ => ?_
  have hr1' : Rest clob64 s0 s1 := hr1.mono (by decide)
  have hc1 : Ctx b s1 := hc.of_rest hr1' (by decide)
  have hf1 : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s1.mem := by rw [hm1]; exact Frame.refl _ _
  refine WP.append (ldN_ok hx hx8 hy hy8 ht.lt 0 hc1 hf1) fun s2 ⟨k2, e2⟩ => ?_
  have r2 := kr k2 (by decide)
  refine WP.append (mulN_ok ts 0) fun s3 ⟨e3, k3⟩ => ?_
  have r3 := kr k3 (by decide)
  have hc3 : Ctx b s3 := hc1.of_rest (r2.trans r3) (by decide)
  have hf3 : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s3.mem := by rw [k3.2.1, k2.2.1]; exact hf1
  refine WP.append (ldN_ok hx hx8 hy hy8 ht.lt 1 hc3 hf3) fun s4 ⟨k4, e4'⟩ => ?_
  have r4 := kr k4 (by decide)
  have r14 := hr1'.trans (r2.trans (r3.trans r4))
  have hacc : ∀ r ∈ [Reg.a4, .a5, .a6], s4.gpr r = s1.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [k4.1 _ (by rcases hr with rfl | rfl | rfl <;> decide), k3.1 _ (by rcases hr with rfl | rfl | rfl <;> decide),
      k2.1 _ (by rcases hr with rfl | rfl | rfl <;> decide)]
  have hm4 : s4.mem = s0.mem := by rw [k4.2.1, k3.2.1, k2.2.1, hm1]
  have hinit : ColInv b s0 (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i))
      (fun j => dw s0.mem b (y + 8 * j))) (ps c)) 0 s4 :=
    ⟨hc.of_rest r14 (by decide), r14, by rw [hm4]; exact Frame.refl _ _,
      by rw [show rr (0 + 2) = .a6 from rfl, hacc _ (by simp), e6], by
      simp only [accW, colsV, show rr 0 = .a4 from rfl, show rr (0 + 1) = .a5 from rfl, hacc .a4 (by simp),
        hacc .a5 (by simp), e4, e5]; rfl⟩
  have hp0 : Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts
      (pstart (fun c => (ps c).length) 0) s4 := by
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · rw [show pstart (fun c => (ps c).length) 0 = 0 from rfl] at hn ⊢
      have e3' := e3 hn
      rw [show PR 0 = (Reg.a7, Reg.t0) from rfl] at e3' ⊢
      rw [k4.1 .a7 (by decide), k4.1 .t0 (by decide), e3']
      obtain ⟨o1, o2⟩ := e2 hn
      rw [o1, o2]
    · rw [show pstart (fun c => (ps c).length) 0 = 0 from rfl] at hn ⊢
      exact e4' hn
  exact WP.mono (columns_ok (Inv := fun k => Pipe (fun i => dw s0.mem b (x + 8 * i))
      (fun j => dw s0.mem b (y + 8 * j)) ts (pstart (fun c => (ps c).length) k))
    (fun k hk s h hi => pcol_ok hx hx8 hy hy8 ht hk h hi) 14 (Nat.le_refl _) s4 hinit hp0) fun _ h => h.1

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
  refine WP.mono (pipe_ok hx hx8 hy hy8 tab_mul hc) fun s3 h3 => ⟨h3.ctx, h3.rest, h3.frame, ?_⟩
  have hlt : val7 (fun i => dw s0.mem b (x + 8 * i)) * val7 (fun j => dw s0.mem b (y + 8 * j)) <
      (2 ^ 64) ^ 14 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (val7_lt fun i _ => dw_lt _ _ _)
      (val7_lt fun i _ => dw_lt _ _ _))
      (by rw [← Nat.pow_add])
  have e : (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j))) (colPairs c)) =
      mulCs (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) := rfl
  rw [e] at h3
  rw [h3.final (by rw [mulCols_sum]; exact hlt), mulCols_sum, V_eq, V_eq]

end

end

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.X448.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (ACC)

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
  refine WP.append (pipe_ok hx hx8 hx hx8 tab_sq hc) fun s3 h3 => ?_
  rw [← sqCs_eq] at h3
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
