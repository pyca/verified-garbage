module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
import VerifiedGarbage.Proof.X448.RISCV64.R64.Macc
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Mul
public import VerifiedGarbage.Proof.X25519.RISCV64.R64.Mul
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide

/-!
# P-384's field on RISC-V: the twelve words of a product

The twelve words of `[x] · [y]` (`product_ok`) and of `[x]²` (`square_ok`)
at `acc`, for numbers of six doublewords (`val6`), by columns, as X25519's
four-word products (`Proof/X25519/RISCV64/R64/Mul.lean`) are, with six
words where those have four:

* the columns: a column's terms add into the accumulator `rr k, rr (k + 1),
  rr (k + 2)` (`terms_ok`), and its end stores its low word at `acc + 8k`
  (`colEnd_ok`), so that after `k` columns the words below `acc + 8k` and the
  accumulator hold the sum of the first `k` (`ColInv`);
* `pipe acc x y ts` (`pipe_ok`), for a table of terms `ts` (`Tab`): each
  term's sums into the column's accumulator, with the next term's product
  and the one after's operands, which the pipeline (`Pipe`) carries from term
  to term (`pstep_ok`), the terms of a column (`pterms_ok`) and the columns
  (`columns_ok`) by induction;
* `product x y`: `pipe` of every term; the columns sum to the product
  (`mulCols_sum`);
* `square x`: `pipe` of the cross products `a_j a_i` (`j < i`), then each
  word doubled, with the top bit of the
  word below shifted in, plus the word of the squares and the carry
  (`dblStep_ok`); twice the cross products plus the squares are the square
  (`sqCols_sum`).
-/

-- separate module: its proofs cost more than its imports, and its importer's changes need not
-- re-check them

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64.R64 (w rr macc zero3 ld6)
open VG.Impl.X25519.RISCV64.R64 (mulTerm colEnd sqTerm dblStep)
open VG.Proof.X25519.RISCV64.R64 (accW accW_lt accW_congr accW_eq)
open VG.Proof.X448.RISCV64.R64 (clob64 dw dw_lt ld_ok sd_ok dw_write_self dw_write_other
  dw_frame macc_ok rr_ne rr_mem rr_cases rr_clob Keeps.rest tsum tsum_cons tsum_le
  colsV colsV_add zero3_ok lds_ok dbl1_ok dbl2_ok dbl3e_ok dbl3o_ok dbl4_ok cp dbw dq dbw_lt
  dq_lt colsV_dbw)

/-! ## Numbers of six doublewords -/

/-- Six doublewords, lowest first. -/
def val6 (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * (f 4 + 2 ^ 64 * f 5))))

theorem val6_congr {f g : Nat → Nat} (h : ∀ i < 6, f i = g i) : val6 f = val6 g := by
  unfold val6
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide)]

theorem val6_lt {f : Nat → Nat} (h : ∀ i < 6, f i < 2 ^ 64) : val6 f < (2 ^ 64) ^ 6 := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide)
  have := h 3 (by decide); have := h 4 (by decide); have := h 5 (by decide)
  unfold val6; omega_arith

/-- The number of the six doublewords at `o`. -/
abbrev E6 (m : Mem) (b : Addr) (o : Nat) : Nat := val6 fun i => dw m b (o + 8 * i)

/-! ## Columns -/

section
variable {acc : Nat} {b : Addr}

/-- The product's area at `acc`. -/
abbrev AR (acc : Nat) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 acc, 96⟩

/-- After `k` columns, from `s0`: the words below `acc + 8k` and the
accumulator `rr k, rr (k + 1)` (with `rr (k + 2)` zero) hold the sum of the
first `k` columns `cs`; the code changed only `clob64` and `acc`. -/
structure ColInv (acc : Nat) (b : Addr) (s0 : State) (cs : Nat → Nat) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 s0 s
  frame : Frame [AR acc b] s0.mem s.mem
  top : s.gpr (rr (k + 2)) = 0
  val : accW acc s.mem b k + (2 ^ 64) ^ k * ((s.gpr (rr k)).toNat + 2 ^ 64 * (s.gpr (rr (k + 1))).toNat) =
    colsV cs k

/-- The end of column `k`: the low word stored, the register zeroed. -/
theorem colEnd_ok (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0) {s0 : State} {k : Nat} (hk : k < 12)
    {s : State} (hc : Ctx b s) (hr : Rest clob64 s0 s) (hf : Frame [AR acc b] s0.mem s.mem)
    {cs : Nat → Nat}
    (hv : accW acc s.mem b k + (2 ^ 64) ^ k * val3 s (rr k) (rr (k + 1)) (rr (k + 2)) = colsV cs (k + 1)) :
    WP isa (.block (colEnd acc k)) s fun s' => ColInv acc b s0 cs (k + 1) s' ∧
      ∀ r, r ≠ rr k → s'.gpr r = s.gpr r := by
  obtain ⟨h01, h02, h12, h07, h00, h17, h10, h27, h20, h3⟩ := rr_ne k (by omega)
  unfold colEnd
  refine sd_ok hc (by omega) (by omega) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ?_
  have hm : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (acc + 8 * k)) (s.gpr (rr k)) := by
    rw [u2.mem, u1.mem]
  have hrr : rr k ∈ clob64 := rr_mem k (by omega)
  have hr2 : Rest clob64 s s2 := (u1.rest _).trans (u2.rest (ws := clob64) hrr)
  refine ⟨⟨hc.of_rest hr2 (by decide), hr.trans hr2, ?_, ?_, ?_⟩,
    fun r hr' => by rw [u2.other _ hr', u1.gpr]⟩
  · rw [hm]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains b (by omega) (by omega) (by omega))
  · rw [show k + 1 + 2 = k + 3 by omega, h3, u2.gpr]; rfl
  · have e1 : s2.gpr (rr (k + 1)) = s.gpr (rr (k + 1)) := by rw [u2.other _ (Ne.symm h01), u1.gpr]
    have e2 : s2.gpr (rr (k + 1 + 1)) = s.gpr (rr (k + 2)) := by
      rw [show k + 1 + 1 = k + 2 by omega, u2.other _ (Ne.symm h02), u1.gpr]
    have ea : accW acc s2.mem b k = accW acc s.mem b k := accW_congr fun c hc' => by
      rw [hm, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have ek : dw s2.mem b (acc + 8 * k) = (s.gpr (rr k)).toNat := by rw [hm, dw_write_self]
    rw [accW, ea, ek, e1, e2, ← hv, val3]
    rw [Nat.pow_succ (n := 2 ^ 64)]
    generalize (2 ^ 64) ^ k = K
    generalize (s.gpr (rr k)).toNat = a
    generalize (s.gpr (rr (k + 1))).toNat = c
    generalize (s.gpr (rr (k + 2))).toNat = d
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by decide]
    generalize 2 ^ 64 = W
    grind

/-- A column's terms: from a state with the accumulator `acc`, each term `p`
of `ps` adds `f p` and keeps `Inv`. -/
def TermOk (acc : Nat) (b : Addr) (s0 : State) (k : Nat) (Inv : State → Prop) (f : Nat × Nat → Nat)
    (code : Nat × Nat → List Instr) (p : Nat × Nat) : Prop :=
  ∀ s, Inv s → Ctx b s → Rest clob64 s0 s → Frame [AR acc b] s0.mem s.mem →
    WP isa (.block (code p)) s fun s' => Inv s' ∧ Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [AR acc b] s0.mem s'.mem ∧
      accW acc s'.mem b k = accW acc s.mem b k ∧
      (val3 s (rr k) (rr (k + 1)) (rr (k + 2)) + f p < 2 ^ 192 →
        val3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) + f p)

/-- A column's terms, by induction on them. -/
theorem terms_ok {s0 : State} {k : Nat} {Inv : State → Prop} {f : Nat × Nat → Nat}
    {code : Nat × Nat → List Instr} :
    ∀ (ps : List (Nat × Nat)), (∀ p ∈ ps, TermOk acc b s0 k Inv f code p) → ∀ s, Inv s → Ctx b s →
      Rest clob64 s0 s → Frame [AR acc b] s0.mem s.mem →
      val3 s (rr k) (rr (k + 1)) (rr (k + 2)) + tsum f ps < 2 ^ 192 →
      WP isa (.block (ps.flatMap code)) s fun s' => Inv s' ∧ Ctx b s' ∧ Rest clob64 s0 s' ∧
        Frame [AR acc b] s0.mem s'.mem ∧
        accW acc s'.mem b k = accW acc s.mem b k ∧
        val3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) + tsum f ps
  | [], _, s, hi, hc, hr, hf, _ => WP.block_nil ⟨hi, hc, hr, hf, rfl, by simp [tsum]⟩
  | p :: ps, hok, s, hi, hc, hr, hf, hb => by
    rw [List.flatMap_cons]
    rw [tsum_cons] at hb
    refine WP.append (hok p (List.mem_cons_self ..) s hi hc hr hf) fun s1 ⟨hi1, hc1, hr1, hf1, ha1, hv1⟩ => ?_
    have hv1 := hv1 (by omega)
    refine WP.mono (terms_ok ps (fun q hq => hok q (List.mem_cons_of_mem _ hq)) s1 hi1 hc1 hr1 hf1
      (by omega)) fun s2 ⟨hi2, hc2, hr2, hf2, ha2, hv2⟩ => ⟨hi2, hc2, hr2, hf2, ha2.trans ha1, ?_⟩
    rw [hv2, hv1, tsum_cons]; omega

/-- Column `k`: its terms `ps`, which sum to `cs k`, then its end. -/
theorem column_ok (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0) {s0 : State} {k : Nat} (hk : k < 12)
    {Inv : State → Prop} {f : Nat × Nat → Nat}
    {code : Nat × Nat → List Instr} {cs : Nat → Nat} (ps : List (Nat × Nat))
    (hok : ∀ p ∈ ps, TermOk acc b s0 k Inv f code p) (hcs : cs k = tsum f ps)
    (hbd : tsum f ps < 6 * 2 ^ 128)
    (hinv : ∀ s s', Inv s → (∀ r, r ≠ rr k → s'.gpr r = s.gpr r) → Inv s') {s : State}
    (h : ColInv acc b s0 cs k s) (hi : Inv s) :
    WP isa (.block (ps.flatMap code ++ colEnd acc k)) s fun s' =>
      ColInv acc b s0 cs (k + 1) s' ∧ Inv s' := by
  have hv0 : val3 s (rr k) (rr (k + 1)) (rr (k + 2)) =
      (s.gpr (rr k)).toNat + 2 ^ 64 * (s.gpr (rr (k + 1))).toNat := by
    simp only [val3, h.top]; rfl
  have hl := (s.gpr (rr k)).isLt
  have hh := (s.gpr (rr (k + 1))).isLt
  refine WP.append (terms_ok ps hok s hi h.ctx h.rest h.frame (by rw [hv0]; omega_arith))
    fun s1 ⟨hi1, hc1, hr1, hf1, ha1, hv1⟩ => ?_
  have hwp := colEnd_ok (cs := cs) hA hA8 hk hc1 hr1 hf1 (by
    rw [ha1, hv1, hv0, colsV, ← h.val, hcs, Nat.mul_add]; omega_arith)
  exact WP.mono hwp fun s2 ⟨h2, hk2⟩ => ⟨h2, hinv s1 s2 hi1 hk2⟩

/-- The columns, by induction. -/
theorem columns_ok {s0 : State} {cs : Nat → Nat} {Inv : Nat → State → Prop} {col : Nat → List Instr}
    (hcol : ∀ k < 12, ∀ s, ColInv acc b s0 cs k s → Inv k s →
      WP isa (.block (col k)) s fun s' => ColInv acc b s0 cs (k + 1) s' ∧ Inv (k + 1) s') :
    ∀ n ≤ 12, ∀ s, ColInv acc b s0 cs 0 s → Inv 0 s →
      WP isa (.block ((List.range n).flatMap col)) s fun s' => ColInv acc b s0 cs n s' ∧ Inv n s'
  | 0, _, s, h, hi => WP.block_nil ⟨h, hi⟩
  | n + 1, hn, s, h, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (columns_ok hcol n (by omega) s h hi) fun s1 ⟨h1, hi1⟩ =>
      hcol n (by omega) s1 h1 hi1

/-- After the twelve columns, the words at `acc` are the columns' sum. -/
theorem ColInv.final {s0 : State} {cs : Nat → Nat} {s : State} (h : ColInv acc b s0 cs 12 s)
    (hlt : colsV cs 12 < (2 ^ 64) ^ 12) : accW acc s.mem b 12 = colsV cs 12 := by
  have hv := h.val
  have := accW_lt (acc := acc) s.mem b 8
  generalize (2 ^ 64) ^ 12 = K at *
  generalize accW acc s.mem b 12 = A at *
  generalize (s.gpr (rr 12)).toNat + 2 ^ 64 * (s.gpr (rr (12 + 1))).toNat = C at *
  generalize colsV cs 12 = V at *
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · omega
  · have : K ≤ K * C := Nat.le_mul_of_pos_right _ hC
    omega

/-- The accumulator of column 0, zero. -/
theorem ColInv.init {s0 s : State} {cs : Nat → Nat} (hc : Ctx b s) (hr : Rest clob64 s0 s)
    (hm : s.mem = s0.mem) (e4 : s.gpr .a4 = 0) (e5 : s.gpr .a5 = 0) (e6 : s.gpr .a6 = 0) :
    ColInv acc b s0 cs 0 s :=
  ⟨hc, hr, by rw [hm]; exact Frame.refl _ _, e6, by
    simp only [accW, colsV, show rr 0 = .a4 from rfl, show rr (0 + 1) = .a5 from rfl, e4, e5]; rfl⟩

/-- An element below `acc`, unchanged in a frame of the product's area. -/
theorem dw_acc (hA : acc + 96 ≤ 2048) {m m' : Mem} (hf : Frame [AR acc b] m m') {d : Nat}
    (hd : d + 8 ≤ acc) :
    dw m' b d = dw m b d :=
  dw_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl hd) (by omega) (by omega)

end

/-! ## The product -/

section
variable {acc : Nat} {b : Addr}

/-- The columns of a product: column `k` is the sum of `a_i b_j` with `i + j = k`. -/
def mulF (X Y : Nat → Nat) (p : Nat × Nat) : Nat := X p.1 * Y p.2

def mulCs (X Y : Nat → Nat) (k : Nat) : Nat := tsum (mulF X Y) (colPairs k)

/-- A cross term's value: `a_j a_i` for the term `(i, j)`. -/
def sqF (X : Nat → Nat) (p : Nat × Nat) : Nat := X p.2 * X p.1

/-- The columns of the cross products. -/
def sqCs (X : Nat → Nat) (k : Nat) : Nat := tsum (sqF X) (sqPairs k)

theorem sqCs_eq (X : Nat → Nat) : sqCs X = fun k => tsum (mulF X X) (sqPairs k) := by
  funext k; unfold sqCs tsum; congr 1; exact List.map_congr_left fun p _ => Nat.mul_comm _ _

theorem mulF_le (X Y : Nat → Nat) (hX : ∀ i, X i < 2 ^ 64) (hY : ∀ j, Y j < 2 ^ 64) (p : Nat × Nat) :
    mulF X Y p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := hX p.1; omega) (by have := hY p.2; omega)

theorem tsum_mul_lt6 {X Y : Nat → Nat} (hX : ∀ i, X i < 2 ^ 64) (hY : ∀ j, Y j < 2 ^ 64)
    {ps : List (Nat × Nat)} (hl : ps.length ≤ 6) : tsum (mulF X Y) ps < 6 * 2 ^ 128 := by
  have := tsum_le (ps := ps) fun p _ => mulF_le X Y hX hY p
  have : ps.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) ≤ 6 * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) :=
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
theorem regs_acc : ∀ k < 15, ∀ e < 2,
    rr k ≠ (PR e).1 ∧ rr k ≠ (PR e).2 ∧ rr k ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧ rr k ∉ [Reg.a1, .a2] := by
  decide

/-- The registers a step's sums write, apart from the next product's and the operands. -/
theorem regs_sum : ∀ k < 12, ∀ e < 2,
    (PR (e + 1)).1 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] ∧
    (PR (e + 1)).2 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] ∧
    Reg.a1 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] ∧
    Reg.a2 ∉ [rr k, rr (k + 1), rr (k + 2), (PR e).1, (PR e).2] := by decide

theorem pstart_succ (cs : Nat → Nat) (k : Nat) : pstart cs (k + 1) = pstart cs k + cs k := by
  simp [pstart, List.range_succ]

/-- What the code of a table of terms `ts` needs: its terms are column `k`'s
pairs `ps k` in order, from `pstart` on, with words below 7. -/
structure Tab (ts : List (Nat × Nat × Nat)) (ps : Nat → List (Nat × Nat)) : Prop where
  take : ∀ k < 12, ∀ m < (ps k).length,
    (ps k).take (m + 1) = (ps k).take m ++ [(tm ts (pstart (fun c => (ps c).length) k + m)).2]
  le : ∀ k < 12, pstart (fun c => (ps c).length) k + (ps k).length ≤ ts.length
  lt : ∀ n < ts.length, (tm ts n).2.1 < 6 ∧ (tm ts n).2.2 < 6
  len : ∀ k < 12, (ps k).length ≤ 6
  all : pstart (fun c => (ps c).length) 12 = ts.length

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
theorem ldN_ok {s0 : State} {x y : Nat} (hx : x + 48 ≤ acc) (hx8 : x % 8 = 0) (hy : y + 48 ≤ acc)
    (hy8 : y % 8 = 0) (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0) {ts : List (Nat × Nat × Nat)} (hlt : ∀ n < ts.length, (tm ts n).2.1 < 6 ∧ (tm ts n).2.2 < 6)
    (n : Nat) {s : State} (hc : Ctx b s) (hf : Frame [AR acc b] s0.mem s.mem) :
    WP isa (.block (ldN x y ts n)) s fun s' => Keeps [.a1, .a2] s s' ∧
      (n < ts.length → (s'.gpr .a1).toNat = dw s0.mem b (x + 8 * (tm ts n).2.1) ∧
        (s'.gpr .a2).toNat = dw s0.mem b (y + 8 * (tm ts n).2.2)) := by
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
    · rw [u2.other _ (by decide), u1.gpr]; exact dw_acc hA hf (by omega)
    · rw [u2.gpr, u1.mem]; exact dw_acc hA hf (by omega)
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
theorem pstep_ok {s0 : State} {x y : Nat} (hx : x + 48 ≤ acc) (hx8 : x % 8 = 0) (hy : y + 48 ≤ acc)
    (hy8 : y % 8 = 0) (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0) {ts : List (Nat × Nat × Nat)} (hlt : ∀ n < ts.length, (tm ts n).2.1 < 6 ∧ (tm ts n).2.2 < 6)
    {k n : Nat} (hk : k < 12) (hn : n < ts.length) {s : State} (hc : Ctx b s) (hr : Rest clob64 s0 s)
    (hf : Frame [AR acc b] s0.mem s.mem)
    (hp : Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts n s)
    (hb : val3 s (rr k) (rr (k + 1)) (rr (k + 2)) +
      dw s0.mem b (x + 8 * (tm ts n).2.1) * dw s0.mem b (y + 8 * (tm ts n).2.2) < 2 ^ 192) :
    WP isa (.block (pstep x y ts k n)) s fun s' => Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [AR acc b] s0.mem s'.mem ∧ s'.mem = s.mem ∧
      Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts (n + 1) s' ∧
      val3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) +
        dw s0.mem b (x + 8 * (tm ts n).2.1) * dw s0.mem b (y + 8 * (tm ts n).2.2) := by
  obtain ⟨h01, h02, h12, -⟩ := rr_ne k (by omega)
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
  have hf1 : Frame [AR acc b] s0.mem s1.mem := by rw [k1.2.1]; exact hf
  refine WP.append (ldN_ok hx hx8 hy hy8 hA hA8 hlt (n + 2) hc1 hf1) fun s2 ⟨k2, e2⟩ => ?_
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
theorem pterms_ok {s0 : State} {x y : Nat} (hx : x + 48 ≤ acc) (hx8 : x % 8 = 0) (hy : y + 48 ≤ acc)
    (hy8 : y % 8 = 0) (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0) {ts : List (Nat × Nat × Nat)} {ps : Nat → List (Nat × Nat)} (ht : Tab ts ps)
    {k : Nat} (hk : k < 12) :
    ∀ m ≤ (ps k).length, ∀ s, Ctx b s → Rest clob64 s0 s → Frame [AR acc b] s0.mem s.mem →
      Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts
        (pstart (fun c => (ps c).length) k) s →
      val3 s (rr k) (rr (k + 1)) (rr (k + 2)) < 2 ^ 128 →
      WP isa (.block ((List.range' (pstart (fun c => (ps c).length) k) m).flatMap (pstep x y ts k))) s fun s' =>
        Ctx b s' ∧ Rest clob64 s0 s' ∧ Frame [AR acc b] s0.mem s'.mem ∧ s'.mem = s.mem ∧
        Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts
          (pstart (fun c => (ps c).length) k + m) s' ∧
        val3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) +
          tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j))) ((ps k).take m)
  | 0, _, s, hc, hr, hf, hp, _ => WP.block_nil ⟨hc, hr, hf, rfl, hp, by simp [tsum]⟩
  | m + 1, hm, s, hc, hr, hf, hp, hv => by
    rw [List.range'_concat, Nat.one_mul, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (pterms_ok hx hx8 hy hy8 hA hA8 ht hk m (by omega) s hc hr hf hp hv)
      fun s1 ⟨hc1, hr1, hf1, m1, hp1, hv1⟩ => ?_
    have hX : ∀ i, dw s0.mem b (x + 8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
    have hY : ∀ j, dw s0.mem b (y + 8 * j) < 2 ^ 64 := fun j => dw_lt _ _ _
    have hts := tsum_mul_lt6 hX hY (ps := (ps k).take m)
      (by rw [List.length_take]; exact Nat.le_trans (Nat.min_le_right _ _) (ht.len k hk))
    have hxy : dw s0.mem b (x + 8 * (tm ts (pstart (fun c => (ps c).length) k + m)).2.1) *
        dw s0.mem b (y + 8 * (tm ts (pstart (fun c => (ps c).length) k + m)).2.2) < 2 ^ 128 :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (hX _) (hY _)) (by decide)
    refine WP.mono (pstep_ok hx hx8 hy hy8 hA hA8 ht.lt hk (by have := ht.le k hk; omega) hc1 hr1 hf1 hp1
      (by rw [hv1]; omega)) fun s2 ⟨hc2, hr2, hf2, m2, hp2, hv2⟩ =>
        ⟨hc2, hr2, hf2, m2.trans m1, by rw [← Nat.add_assoc]; exact hp2, ?_⟩
    rw [hv2, hv1, ht.take k hk m (by omega), tsum_snoc]
    simp only [mulF]; omega

/-- Column `k`: its terms, then its end. -/
theorem pcol_ok {s0 : State} {x y : Nat} (hx : x + 48 ≤ acc) (hx8 : x % 8 = 0) (hy : y + 48 ≤ acc)
    (hy8 : y % 8 = 0) (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0) {ts : List (Nat × Nat × Nat)} {ps : Nat → List (Nat × Nat)} (ht : Tab ts ps)
    {k : Nat} (hk : k < 12) {s : State}
    (h : ColInv acc b s0 (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)))
      (ps c)) k s)
    (hp : Pipe (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) ts
      (pstart (fun c => (ps c).length) k) s) :
    WP isa (.block (pcol acc x y ts (fun c => (ps c).length) k)) s fun s' =>
      ColInv acc b s0 (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)))
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
  have hbd := tsum_mul_lt6 hX hY (ht.len k hk)
  obtain ⟨x1, x2, -, z0a⟩ := regs_acc k (by omega) _ (Nat.mod_lt (pstart (fun c => (ps c).length) (k + 1)) (by decide))
  rw [PR_mod] at x1 x2
  unfold pcol
  refine WP.append (pterms_ok hx hx8 hy hy8 hA hA8 ht hk _ (Nat.le_refl _) s h.ctx h.rest h.frame hp
    (by rw [hv0]; omega_arith)) fun s1 ⟨hc1, hr1, hf1, m1, hp1, hv1⟩ => ?_
  rw [List.take_length] at hv1
  rw [← pstart_succ] at hp1
  have hwp := colEnd_ok hA hA8 (cs := fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i))
    (fun j => dw s0.mem b (y + 8 * j))) (ps c)) hk hc1 hr1 hf1 (by
      rw [show accW acc s1.mem b k = accW acc s.mem b k by rw [m1], hv1, hv0, colsV, ← h.val, Nat.mul_add]; omega_arith)
  exact WP.mono hwp fun s2 ⟨h2, g2⟩ => ⟨h2, hp1.of (g2 _ (Ne.symm x1)) (g2 _ (Ne.symm x2))
    (g2 _ fun e => z0a (by rw [← e]; simp)) (g2 _ fun e => z0a (by rw [← e]; simp))⟩

/-- `pipe acc x y ts`: the columns of the terms `ts` at `acc`. -/
theorem pipe_ok {s0 : State} {x y : Nat} (hx : x + 48 ≤ acc) (hx8 : x % 8 = 0) (hy : y + 48 ≤ acc)
    (hy8 : y % 8 = 0) (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0) {ts : List (Nat × Nat × Nat)} {ps : Nat → List (Nat × Nat)} (ht : Tab ts ps)
    (hc : Ctx b s0) :
    WP isa (.block (pipe acc x y ts fun c => (ps c).length)) s0
      (ColInv acc b s0 (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)))
        (ps c)) 12) := by
  have kr : ∀ {rs : List Reg} {s s' : State}, Keeps rs s s' → (∀ r ∈ rs, r ∈ clob64) → Rest clob64 s s' :=
    fun k hs => (Keeps.rest k).mono hs
  unfold pipe
  simp only [List.append_assoc]
  refine WP.append zero3_ok fun s1 ⟨e4, e5, e6, hr1, hm1⟩ => ?_
  have hr1' : Rest clob64 s0 s1 := hr1.mono (by decide)
  have hc1 : Ctx b s1 := hc.of_rest hr1' (by decide)
  have hf1 : Frame [AR acc b] s0.mem s1.mem := by rw [hm1]; exact Frame.refl _ _
  refine WP.append (ldN_ok hx hx8 hy hy8 hA hA8 ht.lt 0 hc1 hf1) fun s2 ⟨k2, e2⟩ => ?_
  have r2 := kr k2 (by decide)
  refine WP.append (mulN_ok ts 0) fun s3 ⟨e3, k3⟩ => ?_
  have r3 := kr k3 (by decide)
  have hc3 : Ctx b s3 := hc1.of_rest (r2.trans r3) (by decide)
  have hf3 : Frame [AR acc b] s0.mem s3.mem := by rw [k3.2.1, k2.2.1]; exact hf1
  refine WP.append (ldN_ok hx hx8 hy hy8 hA hA8 ht.lt 1 hc3 hf3) fun s4 ⟨k4, e4'⟩ => ?_
  have r4 := kr k4 (by decide)
  have r14 := hr1'.trans (r2.trans (r3.trans r4))
  have hacc : ∀ r ∈ [Reg.a4, .a5, .a6], s4.gpr r = s1.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [k4.1 _ (by rcases hr with rfl | rfl | rfl <;> decide), k3.1 _ (by rcases hr with rfl | rfl | rfl <;> decide),
      k2.1 _ (by rcases hr with rfl | rfl | rfl <;> decide)]
  have hm4 : s4.mem = s0.mem := by rw [k4.2.1, k3.2.1, k2.2.1, hm1]
  have hinit : ColInv acc b s0 (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i))
      (fun j => dw s0.mem b (y + 8 * j))) (ps c)) 0 s4 :=
    ColInv.init (hc.of_rest r14 (by decide)) r14 hm4 (by rw [hacc .a4 (by simp), e4])
      (by rw [hacc .a5 (by simp), e5]) (by rw [hacc .a6 (by simp), e6])
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
    (fun k hk s h hi => pcol_ok hx hx8 hy hy8 hA hA8 ht hk h hi) 12 (Nat.le_refl _) s4 hinit hp0) fun _ h => h.1

/-- The columns sum to the product. -/
theorem mulCols_sum (X Y : Nat → Nat) : colsV (mulCs X Y) 12 = val6 X * val6 Y := by
  simp only [colsV, val6]
  generalize 2 ^ 64 = B
  simp only [mulCs, colPairs, tsum, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mulF, Nat.reduceSub,
    Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  grind

/-- `product acc x y`: the twelve words of `[x] · [y]` at `acc`. -/
theorem product_ok {x y : Nat} (hx : x + 48 ≤ acc) (hy : y + 48 ≤ acc) (hA : acc + 96 ≤ 2048)
    (hA8 : acc % 8 = 0) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (product acc x y)) s0 fun s' => Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [AR acc b] s0.mem s'.mem ∧ accW acc s'.mem b 12 = E6 s0.mem b x * E6 s0.mem b y := by
  refine WP.mono (pipe_ok hx hx8 hy hy8 hA hA8 tab_mul hc) fun s3 h3 => ⟨h3.ctx, h3.rest, h3.frame, ?_⟩
  have e : (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j))) (colPairs c)) =
      mulCs (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) := rfl
  rw [e] at h3
  have hlt : val6 (fun i => dw s0.mem b (x + 8 * i)) * val6 (fun j => dw s0.mem b (y + 8 * j)) <
      (2 ^ 64) ^ 12 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (val6_lt fun i _ => dw_lt _ _ _)
      (val6_lt fun i _ => dw_lt _ _ _))
      (by rw [← Nat.pow_add])
  rw [h3.final (by rw [mulCols_sum]; exact hlt), mulCols_sum]

end

/-! ## The square -/

section
variable {acc : Nat} {b : Addr}

/-- The squares `a_i²` at `2¹²⁸ⁱ`. -/
def dsq (X : Nat → Nat) : Nat :=
  X 0 * X 0 + (2 ^ 64) ^ 2 * (X 1 * X 1) + (2 ^ 64) ^ 4 * (X 2 * X 2) + (2 ^ 64) ^ 6 * (X 3 * X 3) +
    (2 ^ 64) ^ 8 * (X 4 * X 4) + (2 ^ 64) ^ 10 * (X 5 * X 5)

/-- Twice the cross products' columns, plus the squares, are the square. -/
theorem sqCols_sum (X : Nat → Nat) : 2 * colsV (sqCs X) 12 + dsq X = val6 X * val6 X := by
  simp only [colsV, val6, dsq]
  generalize 2 ^ 64 = B
  simp only [sqCs, sqPairs, colPairs, tsum, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil,
    List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sqF, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  grind

/-- The words of the squares are the squares. -/
theorem colsV_dq (X : Nat → Nat) : colsV (dq X) 12 = dsq X := by
  simp only [colsV, dq, dsq]
  simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]
  have h0 := Nat.mod_add_div (X 0 * X 0) (2 ^ 64)
  have h1 := Nat.mod_add_div (X 1 * X 1) (2 ^ 64)
  have h2 := Nat.mod_add_div (X 2 * X 2) (2 ^ 64)
  have h3 := Nat.mod_add_div (X 3 * X 3) (2 ^ 64)
  have h4 := Nat.mod_add_div (X 4 * X 4) (2 ^ 64)
  have h5 := Nat.mod_add_div (X 5 * X 5) (2 ^ 64)
  generalize X 0 * X 0 % 2 ^ 64 = l0 at *
  generalize X 1 * X 1 % 2 ^ 64 = l1 at *
  generalize X 2 * X 2 % 2 ^ 64 = l2 at *
  generalize X 3 * X 3 % 2 ^ 64 = l3 at *
  generalize X 4 * X 4 % 2 ^ 64 = l4 at *
  generalize X 5 * X 5 % 2 ^ 64 = l5 at *
  generalize X 0 * X 0 / 2 ^ 64 = u0 at *
  generalize X 1 * X 1 / 2 ^ 64 = u1 at *
  generalize X 2 * X 2 / 2 ^ 64 = u2 at *
  generalize X 3 * X 3 / 2 ^ 64 = u3 at *
  generalize X 4 * X 4 / 2 ^ 64 = u4 at *
  generalize X 5 * X 5 / 2 ^ 64 = u5 at *
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5]
  generalize 2 ^ 64 = B
  grind

/-- Before step `k` of the doubling, from `s0` (the start of `square x`):
the words of `X` from `k` on unchanged (`C`), `X`'s word `k - 1` in `a5`, the
high word of the last square in `t3` (for odd `k`), the carry in `a4`, and
the words below `k` with the carry the first `k` words of the square. -/
structure DblInv (acc : Nat) (b : Addr) (s0 : State) (x : Nat) (C : Nat → Nat) (k : Nat) (s : State) :
    Prop where
  ctx : Ctx b s
  rest : Rest clob64 s0 s
  frame : Frame [AR acc b] s0.mem s.mem
  hi : ∀ i, k ≤ i → i < 12 → dw s.mem b (acc + 8 * i) = C i
  prev : (s.gpr .a5).toNat = if k = 0 then 0 else C (k - 1)
  sqhi : k % 2 = 1 → (s.gpr .t3).toNat =
    dw s0.mem b (x + 8 * (k / 2)) * dw s0.mem b (x + 8 * (k / 2)) / 2 ^ 64
  cy : (s.gpr .a4).toNat ≤ 2
  val : accW acc s.mem b k + (2 ^ 64) ^ k * (s.gpr .a4).toNat =
    colsV (fun c => dbw C c + dq (fun i => dw s0.mem b (x + 8 * i)) c) k

/-- The end of step `k`: the carry added, the word stored. -/
theorem dblEnd_ok (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0) {s0 : State} {x : Nat} {C : Nat → Nat}
    (hC : ∀ i, C i < 2 ^ 64) {k : Nat} (hk : k < 12) {s s4 : State}
    (h : DblInv acc b s0 x C k s) (hc4 : Ctx b s4) (hr4 : Rest clob64 s s4) (hm4 : s4.mem = s.mem)
    (h4 : s4.gpr .a4 = s.gpr .a4) (h5 : (s4.gpr .a5).toNat = C k)
    (hv : (s4.gpr .a6).toNat + 2 ^ 64 * (s4.gpr .a7).toNat =
      dbw C k + dq (fun i => dw s0.mem b (x + 8 * i)) k)
    (ht : (k + 1) % 2 = 1 → (s4.gpr .t3).toNat =
      dw s0.mem b (x + 8 * ((k + 1) / 2)) * dw s0.mem b (x + 8 * ((k + 1) / 2)) / 2 ^ 64) :
    WP isa (.block (([.add .a6 .a6 .a4, .sltu .t0 .a6 .a4, .add .a4 .a7 .t0] : List Instr) ++
      ([.store .d .a6 .a3 (acc + 8 * k)] : List Instr))) s4 (DblInv acc b s0 x C (k + 1)) := by
  have hb1 := dbw_lt hC k
  have hb2 := dq_lt (X := fun i => dw s0.mem b (x + 8 * i)) (fun i => dw_lt _ _ _) k
  have h7 : (s4.gpr .a7).toNat ≤ 1 := by
    have := (s4.gpr .a6).isLt
    omega
  refine WP.append dbl4_ok fun s5 ⟨e5, k5⟩ => ?_
  have hr5 : Rest clob64 s4 s5 := Rest.mono (ws' := clob64) (Keeps.rest k5) (by decide)
  have hc5 : Ctx b s5 := hc4.of_rest hr5 (by decide)
  refine sd_ok hc5 (by omega) (by omega) fun s6 u6 => WP.block_nil ?_
  have hm6 : s6.mem = s.mem.writeW (b + BitVec.ofNat 64 (acc + 8 * k)) (s5.gpr .a6) := by
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
  · have ea : accW acc s6.mem b k = accW acc s.mem b k := accW_congr fun c hc' => by
      rw [hm6, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have ek : dw s6.mem b (acc + 8 * k) = (s5.gpr .a6).toNat := by rw [hm6, dw_write_self]
    rw [accW, ea, ek, colsV, ← h.val, Nat.pow_succ (n := 2 ^ 64)]
    rw [u6.gpr] at hv6 ⊢
    generalize (2 ^ 64) ^ k = K at *
    generalize (s5.gpr .a6).toNat = a at *
    generalize (s5.gpr .a4).toNat = c at *
    generalize (s.gpr .a4).toNat = d at *
    generalize dbw C k + dq (fun i => dw s0.mem b (x + 8 * i)) k = t at *
    generalize 2 ^ 64 = W at *
    grind

theorem dblStep_ok {x : Nat} (hx : x + 48 ≤ acc) (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0)
    (hx8 : x % 8 = 0) {s0 : State} {C : Nat → Nat}
    (hC : ∀ i, C i < 2 ^ 64) {k : Nat} (hk : k < 12) {s : State} (h : DblInv acc b s0 x C k s) :
    WP isa (.block (dblStep acc x k)) s (DblInv acc b s0 x C (k + 1)) := by
  have hc := h.ctx
  have e : dblStep acc x k = [.shift .srl .d .a7 .a5 63] ++ (.load .d .a5 .a3 (acc + 8 * k) ::
      ([.shift .sll .d .a6 .a5 1, .logic .or .a6 .a6 .a7] ++
        ((if k % 2 = 0 then
          .load .d .t3 .a3 (x + 8 * (k / 2)) :: [.mul .t0 .t3 .t3, .mulhu .t3 .t3 .t3,
            .add .a6 .a6 .t0, .sltu .a7 .a6 .t0]
         else [.add .a6 .a6 .t3, .sltu .a7 .a6 .t3]) ++
        ([.add .a6 .a6 .a4, .sltu .t0 .a6 .a4, .add .a4 .a7 .t0] ++
          [.store .d .a6 .a3 (acc + 8 * k)])))) := by
    simp only [dblStep, List.cons_append, List.nil_append]
  rw [e]
  refine WP.append dbl1_ok fun s1 ⟨e1, k1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest (Rest.mono (ws' := clob64) (Keeps.rest k1) (by decide)) (by decide)
  refine ld_ok hc1 (by omega) (by omega) fun s2 u2 => ?_
  refine WP.append dbl2_ok fun s3 ⟨e3, k3⟩ => ?_
  have hck : (s2.gpr .a5).toNat = C k := by
    rw [u2.gpr, show (s1.mem.readW _ 64).toNat = dw s1.mem b (acc + 8 * k) from rfl, k1.2.1]
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
  have hk2 : x + 8 * (k / 2) + 8 ≤ acc := by omega
  by_cases hpar : k % 2 = 0
  · rw [ite_eq_left hpar, List.cons_append]
    refine ld_ok hc3 (by omega) (by omega) fun s4 u4 => ?_
    refine WP.append dbl3e_ok fun s5 ⟨e5, f5, k5⟩ => ?_
    have hr5 : Rest clob64 s3 s5 := (u4.rest (by decide)).trans
      (Rest.mono (ws' := clob64) (Keeps.rest k5) (by decide))
    have ht4 : (s4.gpr .t3).toNat = dw s0.mem b (x + 8 * (k / 2)) := by
      rw [u4.gpr, show (s3.mem.readW _ 64).toNat = dw s3.mem b (x + 8 * (k / 2)) from rfl, hm3]
      exact dw_acc hA h.frame hk2
    refine dblEnd_ok hA hA8 hC hk h (hc3.of_rest hr5 (by decide)) (hr3.trans hr5)
      (by rw [k5.2.1, u4.mem, hm3]) (by rw [k5.1 _ (by decide), u4.other _ (by decide), h4s])
      (by rw [k5.1 _ (by decide), u4.other _ (by decide), h5s]) ?_ ?_
    · rw [e5, u4.other _ (by decide), ha6, ht4, dq, ite_eq_left hpar]
    · intro _
      rw [f5, ht4, show (k + 1) / 2 = k / 2 by omega]
  · rw [ite_eq_right hpar]
    refine WP.append dbl3o_ok fun s5 ⟨e5, k5⟩ => ?_
    have hr5 : Rest clob64 s3 s5 := Rest.mono (ws' := clob64) (Keeps.rest k5) (by decide)
    have ht3 : (s3.gpr .t3).toNat =
        dw s0.mem b (x + 8 * (k / 2)) * dw s0.mem b (x + 8 * (k / 2)) / 2 ^ 64 := by
      rw [k3.1 _ (by decide), u2.other _ (by decide), k1.1 _ (by decide)]
      exact h.sqhi (by omega)
    refine dblEnd_ok hA hA8 hC hk h (hc3.of_rest hr5 (by decide)) (hr3.trans hr5)
      (by rw [k5.2.1, hm3]) (by rw [k5.1 _ (by decide), h4s])
      (by rw [k5.1 _ (by decide), h5s]) ?_ (fun h' => absurd h' (by omega))
    rw [e5, ha6, ht3, dq, ite_eq_right hpar]

/-- The steps of the doubling, by induction. -/
theorem dbls_ok {x : Nat} (hx : x + 48 ≤ acc) (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0)
    (hx8 : x % 8 = 0) {s0 : State} {C : Nat → Nat} (hC : ∀ i, C i < 2 ^ 64) :
    ∀ n ≤ 12, ∀ s, DblInv acc b s0 x C 0 s →
      WP isa (.block ((List.range n).flatMap (dblStep acc x))) s (DblInv acc b s0 x C n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (dbls_ok hx hA hA8 hx8 hC n (by omega) s h) fun s1 h1 =>
      dblStep_ok hx hA hA8 hx8 hC (by omega) h1

/-- `square acc x`: the twelve words of `[x]²` at `acc`. -/
theorem square_ok {x : Nat} (hx : x + 48 ≤ acc) (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0)
    (hx8 : x % 8 = 0) {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (square acc x)) s0 fun s' => Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [AR acc b] s0.mem s'.mem ∧ accW acc s'.mem b 12 = E6 s0.mem b x * E6 s0.mem b x := by
  have hX : ∀ i, dw s0.mem b (x + 8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
  unfold square
  simp only [List.append_assoc]
  refine WP.append (pipe_ok hx hx8 hx hx8 hA hA8 tab_sq hc) fun s3 h3 => ?_
  rw [← sqCs_eq] at h3
  have hsum := sqCols_sum fun i => dw s0.mem b (x + 8 * i)
  have hlt : val6 (fun i => dw s0.mem b (x + 8 * i)) * val6 (fun i => dw s0.mem b (x + 8 * i)) <
      (2 ^ 64) ^ 12 := by
    rw [show (12 : Nat) = 6 + 6 from rfl, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (val6_lt fun i _ => hX i) (val6_lt fun i _ => hX i)
  have hfin := h3.final (by omega)
  refine wp_li (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => ?_
  have hr5 : Rest clob64 s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  have hm5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  have hd0 : DblInv acc b s0 x (fun i => dw s3.mem b (acc + 8 * i)) 0 s5 :=
    ⟨h3.ctx.of_rest hr5 (by decide), h3.rest.trans hr5, by rw [hm5]; exact h3.frame,
      fun i _ _ => by rw [hm5], by rw [u5.other _ (by decide), u4.gpr]; rfl, fun h' => absurd h' (by decide),
      by rw [u5.gpr]; decide, by rw [u5.gpr]; rfl⟩
  refine WP.mono (dbls_ok hx hA hA8 hx8 (fun i => dw_lt _ _ _) 12 (Nat.le_refl _) s5 hd0) fun s6 h6 =>
    ⟨h6.ctx, h6.rest, h6.frame, ?_⟩
  have hv := h6.val
  rw [colsV_add, colsV_dq] at hv
  have hd := colsV_dbw (C := fun i => dw s3.mem b (acc + 8 * i)) (fun i => dw_lt _ _ _) 11
  rw [← accW_eq, hfin] at hd
  have := accW_lt (acc := acc) s6.mem b 8
  generalize (2 ^ 64) ^ 12 = K at *
  generalize accW acc s6.mem b 12 = A at *
  generalize val6 (fun i => dw s0.mem b (x + 8 * i)) * val6 (fun i => dw s0.mem b (x + 8 * i)) = Q at *
  generalize colsV (dbw fun i => dw s3.mem b (acc + 8 * i)) 12 = D at *
  generalize colsV (sqCs fun i => dw s0.mem b (x + 8 * i)) 12 = S at *
  generalize dsq (fun i => dw s0.mem b (x + 8 * i)) = E at *
  generalize (s6.gpr .a4).toNat = c at *
  generalize dw s3.mem b (acc + 8 * 11) / 2 ^ 63 = t at *
  rcases Nat.eq_zero_or_pos (c + t) with h0 | hpos
  · have : c = 0 := by omega
    have : t = 0 := by omega
    subst_vars; omega
  · have : K ≤ K * (c + t) := Nat.le_mul_of_pos_right _ hpos
    rw [Nat.mul_add] at this
    omega

end

end VG.Proof.Weierstrass.RISCV64.P384Field
