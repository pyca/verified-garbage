module

public import VerifiedGarbage.Impl.X25519.RISCV64.R64
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
import VerifiedGarbage.Proof.X448.RISCV64.R64.Macc
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Mul
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide

/-!
# X25519 on RISC-V, 64-bit limbs: the eight words of a product

A field element's 32 bytes at `o` are four doublewords as well as eight words:
`V` is `val4` of the doublewords (`V_eq4`). The eight words of `[x] · [y]`
(`product_ok`) and of `[x]²` (`square_ok`) at `acc`, by columns, as X448's
(`Proof/X448/RISCV64/R64/Mul.lean`) are, whose lemmas about registers,
doublewords and a term (`macc_ok`) these use:

* the columns: a column's terms add into the accumulator `rr k, rr (k + 1),
  rr (k + 2)` (`terms_ok`), and its end stores its low word at `acc + 8k`
  (`colEnd_ok`), so that after `k` columns the words below `acc + 8k` and the
  accumulator hold the sum of the first `k` (`ColInv`);
* `product x y`: `b₀–b₃` in `w 0`–`w 3`, each term `a_i b_j` with `a_i`
  loaded (`mulTerm_ok`); the columns sum to the product (`mulCols_sum`);
* `square x`: the cross products `a_j a_i` (`j < i`) with `a₀–a₃` in
  registers (`sqTerm_ok`), then each word doubled, with the top bit of the
  word below shifted in, plus the word of the squares and the carry
  (`dblStep_ok`); twice the cross products plus the squares are the square
  (`sqCols_sum`).
-/

-- separate module: its proofs (about 3 s) cost more than its imports, and its importer's
-- changes need not re-check them

@[expose] public section

namespace VG.Proof.X25519.RISCV64.R64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.X25519.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64.R64 (w rr macc zero3)
open VG.Proof.X448.RISCV64.R64 (clob64 dw dw_lt dw_split ew ld_ok sd_ok dw_write_self dw_write_other
  dw_frame macc_ok nat_mulhi_lt mulhi_lt rr_ne rr_mem rr_cases rr_clob Keeps.rest tsum tsum_cons tsum_le
  colsV colsV_add zero3_ok lds_ok w_ne w_clob dbl1_ok dbl2_ok dbl3e_ok dbl3o_ok dbl4_ok cp dbw dq dbw_lt
  dq_lt colsV_dbw)

/-! ## Elements as doublewords -/

/-- Four doublewords, lowest first. -/
def val4 (f : Nat → Nat) : Nat := f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * f 3))

theorem val4_congr {f g : Nat → Nat} (h : ∀ i < 4, f i = g i) : val4 f = val4 g := by
  unfold val4
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

theorem val4_lt {f : Nat → Nat} (h : ∀ i < 4, f i < 2 ^ 64) : val4 f < (2 ^ 64) ^ 4 := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide)
  have := h 3 (by decide)
  unfold val4; omega_arith

/-- The number of an element is its four doublewords. -/
theorem V_eq4 (m : Mem) (P : Addr) (o : Nat) : V m P o = val4 (ew m P o) := by
  simp only [V, val4, ew, val32, limb, dw_split]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
  omega_arith

/-! ## Columns -/

section
variable {acc : Nat} {b : Addr}

/-- The words below `acc + 8k`. -/
def accW (acc : Nat) (m : Mem) (b : Addr) : Nat → Nat
  | 0 => 0
  | k + 1 => accW acc m b k + (2 ^ 64) ^ k * dw m b (acc + 8 * k)

theorem accW_lt (m : Mem) (b : Addr) : ∀ k, accW acc m b k < (2 ^ 64) ^ k
  | 0 => by simp [accW]
  | k + 1 => by
    have := accW_lt m b k
    have := dw_lt m b (acc + 8 * k)
    rw [accW, Nat.pow_succ (n := 2 ^ 64)]
    calc accW acc m b k + (2 ^ 64) ^ k * dw m b (acc + 8 * k)
        < (2 ^ 64) ^ k + (2 ^ 64) ^ k * dw m b (acc + 8 * k) := by omega
      _ = (2 ^ 64) ^ k * (dw m b (acc + 8 * k) + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ (2 ^ 64) ^ k * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega)

theorem accW_congr {m m' : Mem} : ∀ {k}, (∀ c < k, dw m' b (acc + 8 * c) = dw m b (acc + 8 * c)) →
    accW acc m' b k = accW acc m b k
  | 0, _ => rfl
  | k + 1, h => by
    rw [accW, accW, accW_congr (fun c hc => h c (by omega)), h k (by omega)]

theorem accW_eq (m : Mem) (b : Addr) : ∀ k, accW acc m b k = colsV (fun c => dw m b (acc + 8 * c)) k
  | 0 => rfl
  | k + 1 => by rw [accW, colsV, accW_eq m b k]

/-- The product's area at `acc`. -/
abbrev AR (acc : Nat) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 acc, 64⟩

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
theorem colEnd_ok (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0) {s0 : State} {k : Nat} (hk : k < 8)
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
theorem column_ok (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0) {s0 : State} {k : Nat} (hk : k < 8)
    {Inv : State → Prop} {f : Nat × Nat → Nat}
    {code : Nat × Nat → List Instr} {cs : Nat → Nat} (ps : List (Nat × Nat))
    (hok : ∀ p ∈ ps, TermOk acc b s0 k Inv f code p) (hcs : cs k = tsum f ps)
    (hbd : tsum f ps < 4 * 2 ^ 128)
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
    (hcol : ∀ k < 8, ∀ s, ColInv acc b s0 cs k s → Inv k s →
      WP isa (.block (col k)) s fun s' => ColInv acc b s0 cs (k + 1) s' ∧ Inv (k + 1) s') :
    ∀ n ≤ 8, ∀ s, ColInv acc b s0 cs 0 s → Inv 0 s →
      WP isa (.block ((List.range n).flatMap col)) s fun s' => ColInv acc b s0 cs n s' ∧ Inv n s'
  | 0, _, s, h, hi => WP.block_nil ⟨h, hi⟩
  | n + 1, hn, s, h, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (columns_ok hcol n (by omega) s h hi) fun s1 ⟨h1, hi1⟩ =>
      hcol n (by omega) s1 h1 hi1

/-- After the eight columns, the words at `acc` are the columns' sum. -/
theorem ColInv.final {s0 : State} {cs : Nat → Nat} {s : State} (h : ColInv acc b s0 cs 8 s)
    (hlt : colsV cs 8 < (2 ^ 64) ^ 8) : accW acc s.mem b 8 = colsV cs 8 := by
  have hv := h.val
  have := accW_lt (acc := acc) s.mem b 8
  generalize (2 ^ 64) ^ 8 = K at *
  generalize accW acc s.mem b 8 = A at *
  generalize (s.gpr (rr 8)).toNat + 2 ^ 64 * (s.gpr (rr (8 + 1))).toNat = C at *
  generalize colsV cs 8 = V at *
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
theorem dw_acc (hA : acc + 64 ≤ 2048) {m m' : Mem} (hf : Frame [AR acc b] m m') {d : Nat}
    (hd : d + 8 ≤ acc) :
    dw m' b d = dw m b d :=
  dw_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl hd) (by omega) (by omega)

end

/-! ## The product -/

section
variable {acc : Nat} {b : Addr}

/-- `b₀–b₃` in `w 0`–`w 3`. -/
def WRegs (Y : Nat → Nat) (s : State) : Prop := ∀ j < 4, (s.gpr (w j)).toNat = Y j

theorem w_ne' : ∀ i < 4, w i ≠ .a4 ∧ w i ≠ .a5 ∧ w i ≠ .a6 ∧ w i ≠ .a7 ∧ w i ≠ .t0 ∧ w i ∈ clob64 := by
  decide

theorem w_ne_rr (k : Nat) {i : Nat} (hi : i < 4) : w i ≠ rr k ∧ w i ≠ rr (k + 1) ∧
    w i ≠ rr (k + 2) ∧ w i ≠ .a7 ∧ w i ≠ .t0 ∧ w i ∈ clob64 := by
  obtain ⟨h4, h5, h6, h7, h0, hc⟩ := w_ne' i hi
  refine ⟨?_, ?_, ?_, h7, h0, hc⟩ <;>
  · rcases rr_cases (k := _) with e | e | e <;> rw [e] <;> with_reducible assumption

theorem WRegs.of_gpr {Y : Nat → Nat} {s s' : State} (h : WRegs Y s)
    (hg : ∀ j < 4, s'.gpr (w j) = s.gpr (w j)) : WRegs Y s' :=
  fun j hj => by rw [hg j hj]; exact h j hj

/-- The columns of a product: column `k` is the sum of `a_i b_j` with `i + j = k`. -/
def mulF (X Y : Nat → Nat) (p : Nat × Nat) : Nat := X p.1 * Y p.2

def mulCs (X Y : Nat → Nat) (k : Nat) : Nat := tsum (mulF X Y) (colPairs k)

theorem keeps_clob {k : Nat} {s1 s2 : State}
    (k2 : Keeps [rr k, rr (k + 1), rr (k + 2), .a7, .t0] s1 s2) : Rest clob64 s1 s2 :=
  (Keeps.rest k2).mono fun r hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    exacts [rr_clob _, rr_clob _, rr_clob _, by decide, by decide]

/-- A term `a_i b_j` of column `k`. -/
theorem mulTerm_ok {s0 : State} {x : Nat} (hx : x + 32 ≤ acc) (hA : acc + 64 ≤ 2048)
    (hx8 : x % 8 = 0) {Y : Nat → Nat} {k i j : Nat} (hk : k < 8) (hi : i < 4) (hj : j < 4) :
    TermOk acc b s0 k (WRegs Y) (mulF (fun i => dw s0.mem b (x + 8 * i)) Y) (mulTerm x k) (i, j) := by
  intro s hB hc hr hf
  obtain ⟨h01, h02, h12, h07, h00, h17, h10, h27, h20, -⟩ := rr_ne k (by omega)
  obtain ⟨hb0, hb1, hb2, hb7, hbt, hbc⟩ := w_ne_rr k hj
  simp only [mulTerm]
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => ?_
  refine WP.mono (macc_ok h01 h02 h12 h07 h00 h17 h10 h27 h20 (by decide) hb7) fun s2 ⟨e2, k2⟩ => ?_
  have hr2 : Rest clob64 s s2 := (u1.rest (ws := clob64) (by decide)).trans (keeps_clob k2)
  have hm2 : s2.mem = s.mem := by rw [k2.2.1, u1.mem]
  have hv1 : val3 s1 (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) := by
    simp only [val3, u1.other _ h00, u1.other _ h10, u1.other _ h20]
  have ex : (s1.gpr .t0).toNat = dw s0.mem b (x + 8 * i) := by
    rw [u1.gpr]; exact dw_acc hA hf (by omega)
  have ey : (s1.gpr (w j)).toNat = Y j := by
    rw [u1.other _ hbt]; exact hB j hj
  refine ⟨hB.of_gpr fun j' hj' => ?_, hc.of_rest hr2 (by decide), hr.trans hr2, by rw [hm2]; exact hf,
    by rw [hm2], fun hb => ?_⟩
  · obtain ⟨c0, c1, c2, c7, ct, -⟩ := w_ne_rr k hj'
    rw [k2.1 _ (by simp [c0, c1, c2, c7, ct]), u1.other _ ct]
  · rw [e2 (by rw [hv1, ex, ey]; exact hb), hv1, ex, ey]; rfl

theorem colPairs_ok : ∀ k < 8, ∀ p ∈ colPairs k, p.1 < 4 ∧ p.2 < 4 := by decide

theorem colPairs_len : ∀ k < 8, (colPairs k).length ≤ 4 := by decide

theorem mulF_le (X Y : Nat → Nat) (hX : ∀ i, X i < 2 ^ 64) (hY : ∀ j, Y j < 2 ^ 64) (p : Nat × Nat) :
    mulF X Y p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := hX p.1; omega) (by have := hY p.2; omega)

theorem tsum_lt {f : Nat × Nat → Nat} (hf : ∀ p, f p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    {ps : List (Nat × Nat)} (hl : ps.length ≤ 4) : tsum f ps < 4 * 2 ^ 128 := by
  have := tsum_le (ps := ps) fun p _ => hf p
  have : ps.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) ≤ 4 * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) :=
    Nat.mul_le_mul_right _ hl
  omega

/-- Column `k` of `product x y`. -/
theorem mulCol_ok {x : Nat} (hx : x + 32 ≤ acc) (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0)
    (hx8 : x % 8 = 0) {s0 : State} {Y : Nat → Nat} (hY : ∀ j, Y j < 2 ^ 64) {k : Nat} (hk : k < 8)
    {s : State} (h : ColInv acc b s0 (mulCs (fun i => dw s0.mem b (x + 8 * i)) Y) k s)
    (hB : WRegs Y s) :
    WP isa (.block (mulCol acc x k)) s fun s' =>
      ColInv acc b s0 (mulCs (fun i => dw s0.mem b (x + 8 * i)) Y) (k + 1) s' ∧ WRegs Y s' :=
  column_ok hA hA8 hk (colPairs k) (fun p hp => by
      obtain ⟨h1, h2⟩ := colPairs_ok k hk p hp
      exact mulTerm_ok hx hA hx8 hk h1 h2) rfl
    (tsum_lt (mulF_le _ _ (fun i => dw_lt _ _ _) hY) (colPairs_len k hk))
    (fun _ _ hB' hg => hB'.of_gpr fun j hj => hg _ (w_ne_rr k hj).1) h hB

/-- The columns sum to the product. -/
theorem mulCols_sum (X Y : Nat → Nat) : colsV (mulCs X Y) 8 = val4 X * val4 Y := by
  simp only [colsV, val4]
  generalize 2 ^ 64 = B
  simp only [mulCs, colPairs, tsum, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mulF, Nat.reduceSub,
    Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  grind

/-- `ld4 o`. -/
theorem ld4_ok {o : Nat} (ho : o + 56 ≤ 2048) (ho8 : o % 8 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (ld4 o)) s fun s' =>
      (∀ i < 4, (s'.gpr (w i)).toNat = dw s.mem b (o + 8 * i)) ∧ Rest clob64 s s' ∧ s'.mem = s.mem :=
  lds_ok ho ho8 4 (by decide) s hc

/-- `product acc x y`: the eight words of `[x] · [y]` at `acc`. -/
theorem product_ok {x y : Nat} (hx : x + 32 ≤ acc) (hy : y + 32 ≤ acc) (hA : acc + 64 ≤ 2048)
    (hA8 : acc % 8 = 0) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (product acc x y)) s0 fun s' => Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [AR acc b] s0.mem s'.mem ∧ accW acc s'.mem b 8 = V s0.mem b x * V s0.mem b y := by
  unfold product
  rw [List.append_assoc]
  refine WP.append (ld4_ok (by omega) hy8 hc) fun s1 ⟨h1, hr1, hm1⟩ => ?_
  refine WP.append zero3_ok fun s2 ⟨e4, e5, e6, hr2, hm2⟩ => ?_
  have hr12 := hr1.trans (hr2.mono (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr12 (by decide)
  have hB : WRegs (fun j => dw s0.mem b (y + 8 * j)) s2 := fun j hj => by
    rw [hr2.gpr _ (by revert hj; revert j; decide), h1 j hj]
  refine WP.mono (columns_ok (cs := mulCs (fun i => dw s0.mem b (x + 8 * i)) fun j => dw s0.mem b (y + 8 * j))
    (Inv := fun _ => WRegs fun j => dw s0.mem b (y + 8 * j)) (col := mulCol acc x)
    (fun k hk s h hi => mulCol_ok (Y := fun j => dw s0.mem b (y + 8 * j)) hx hA hA8 hx8
      (fun j => dw_lt _ _ _) hk h hi) 8 (Nat.le_refl _) s2
    (ColInv.init hc2 hr12 (by rw [hm2, hm1]) e4 e5 e6) hB)
    fun s3 ⟨h3, _⟩ => ⟨h3.ctx, h3.rest, h3.frame, ?_⟩
  have hlt : val4 (fun i => dw s0.mem b (x + 8 * i)) * val4 (fun j => dw s0.mem b (y + 8 * j)) <
      (2 ^ 64) ^ 8 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (val4_lt fun i _ => dw_lt _ _ _)
      (val4_lt fun i _ => dw_lt _ _ _))
      (by rw [← Nat.pow_add])
  rw [h3.final (by rw [mulCols_sum]; exact hlt), mulCols_sum, V_eq4, V_eq4]

end

/-! ## The square -/

section
variable {acc : Nat} {b : Addr}

/-- A cross term's value: `a_j a_i` for the term `(i, j)`. -/
def sqF (X : Nat → Nat) (p : Nat × Nat) : Nat := X p.2 * X p.1

/-- The cross terms of column `k`. -/
def sqPairs (k : Nat) : List (Nat × Nat) := (colPairs k).filter fun p => p.2 < p.1

def sqCs (X : Nat → Nat) (k : Nat) : Nat := tsum (sqF X) (sqPairs k)

theorem sqPairs_ok : ∀ k < 8, ∀ p ∈ sqPairs k, p.2 < 4 ∧ p.1 < 4 := by decide

theorem sqPairs_len : ∀ k < 8, (sqPairs k).length ≤ 4 := by decide

/-- A cross term `a_j a_i` of column `k`. -/
theorem sqTerm_ok {s0 : State} {X : Nat → Nat} {k i j : Nat} (hk : k < 8) (hi : i < 4)
    (hj : j < 4) :
    TermOk acc b s0 k (WRegs X) (sqF X) (sqTerm k) (i, j) := by
  intro s hX hc hr hf
  obtain ⟨h01, h02, h12, h07, h00, h17, h10, h27, h20, -⟩ := rr_ne k (by omega)
  obtain ⟨c0, c1, c2, c7, ct, -⟩ := w_ne_rr k hj
  obtain ⟨d0, d1, d2, d7, dt, -⟩ := w_ne_rr k hi
  simp only [sqTerm]
  refine WP.mono (macc_ok h01 h02 h12 h07 h00 h17 h10 h27 h20 c7 d7) fun s2 ⟨e2, k2⟩ =>
    ⟨hX.of_gpr fun i' hi' => ?_, hc.of_rest (keeps_clob k2) (by decide), hr.trans (keeps_clob k2),
      by rw [k2.2.1]; exact hf, by rw [k2.2.1], fun hb => ?_⟩
  · obtain ⟨e0, e1, e2', e7, et, -⟩ := w_ne_rr k hi'
    exact k2.1 _ (by simp [e0, e1, e2', e7, et])
  · have ex := hX j hj
    have ey := hX i hi
    rw [e2 (by rw [ex, ey]; exact hb), ex, ey]; rfl

/-- Column `k` of the cross products. -/
theorem sqCol_ok (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0) {s0 : State} {X : Nat → Nat}
    (hX : ∀ i, X i < 2 ^ 64) {k : Nat} (hk : k < 8) {s : State} (h : ColInv acc b s0 (sqCs X) k s)
    (hR : WRegs X s) :
    WP isa (.block (sqCol acc k)) s fun s' => ColInv acc b s0 (sqCs X) (k + 1) s' ∧ WRegs X s' :=
  column_ok hA hA8 hk (sqPairs k) (fun p hp => by
      obtain ⟨h1, h2⟩ := sqPairs_ok k hk p hp
      exact sqTerm_ok hk h2 h1) rfl
    (tsum_lt (fun p => Nat.mul_le_mul (by have := hX p.2; omega) (by have := hX p.1; omega))
      (sqPairs_len k hk))
    (fun _ _ hR' hg => hR'.of_gpr fun j hj => hg _ (w_ne_rr k hj).1) h hR

/-- The squares `a_i²` at `2¹²⁸ⁱ`. -/
def dsq (X : Nat → Nat) : Nat :=
  X 0 * X 0 + (2 ^ 64) ^ 2 * (X 1 * X 1) + (2 ^ 64) ^ 4 * (X 2 * X 2) + (2 ^ 64) ^ 6 * (X 3 * X 3)

/-- Twice the cross products' columns, plus the squares, are the square. -/
theorem sqCols_sum (X : Nat → Nat) : 2 * colsV (sqCs X) 8 + dsq X = val4 X * val4 X := by
  simp only [colsV, val4, dsq]
  generalize 2 ^ 64 = B
  simp only [sqCs, sqPairs, colPairs, tsum, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil,
    List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sqF, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  grind

/-- The words of the squares are the squares. -/
theorem colsV_dq (X : Nat → Nat) : colsV (dq X) 8 = dsq X := by
  simp only [colsV, dq, dsq]
  simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]
  have h0 := Nat.mod_add_div (X 0 * X 0) (2 ^ 64)
  have h1 := Nat.mod_add_div (X 1 * X 1) (2 ^ 64)
  have h2 := Nat.mod_add_div (X 2 * X 2) (2 ^ 64)
  have h3 := Nat.mod_add_div (X 3 * X 3) (2 ^ 64)
  generalize X 0 * X 0 % 2 ^ 64 = l0 at *
  generalize X 1 * X 1 % 2 ^ 64 = l1 at *
  generalize X 2 * X 2 % 2 ^ 64 = l2 at *
  generalize X 3 * X 3 % 2 ^ 64 = l3 at *
  generalize X 0 * X 0 / 2 ^ 64 = u0 at *
  generalize X 1 * X 1 / 2 ^ 64 = u1 at *
  generalize X 2 * X 2 / 2 ^ 64 = u2 at *
  generalize X 3 * X 3 / 2 ^ 64 = u3 at *
  rw [← h0, ← h1, ← h2, ← h3]
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
  hi : ∀ i, k ≤ i → i < 8 → dw s.mem b (acc + 8 * i) = C i
  prev : (s.gpr .a5).toNat = if k = 0 then 0 else C (k - 1)
  sqhi : k % 2 = 1 → (s.gpr .t3).toNat =
    dw s0.mem b (x + 8 * (k / 2)) * dw s0.mem b (x + 8 * (k / 2)) / 2 ^ 64
  cy : (s.gpr .a4).toNat ≤ 2
  val : accW acc s.mem b k + (2 ^ 64) ^ k * (s.gpr .a4).toNat =
    colsV (fun c => dbw C c + dq (fun i => dw s0.mem b (x + 8 * i)) c) k

/-- The end of step `k`: the carry added, the word stored. -/
theorem dblEnd_ok (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0) {s0 : State} {x : Nat} {C : Nat → Nat}
    (hC : ∀ i, C i < 2 ^ 64) {k : Nat} (hk : k < 8) {s s4 : State}
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

theorem dblStep_ok {x : Nat} (hx : x + 32 ≤ acc) (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0)
    (hx8 : x % 8 = 0) {s0 : State} {C : Nat → Nat}
    (hC : ∀ i, C i < 2 ^ 64) {k : Nat} (hk : k < 8) {s : State} (h : DblInv acc b s0 x C k s) :
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
theorem dbls_ok {x : Nat} (hx : x + 32 ≤ acc) (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0)
    (hx8 : x % 8 = 0) {s0 : State} {C : Nat → Nat} (hC : ∀ i, C i < 2 ^ 64) :
    ∀ n ≤ 8, ∀ s, DblInv acc b s0 x C 0 s →
      WP isa (.block ((List.range n).flatMap (dblStep acc x))) s (DblInv acc b s0 x C n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (dbls_ok hx hA hA8 hx8 hC n (by omega) s h) fun s1 h1 =>
      dblStep_ok hx hA hA8 hx8 hC (by omega) h1

/-- `square acc x`: the eight words of `[x]²` at `acc`. -/
theorem square_ok {x : Nat} (hx : x + 32 ≤ acc) (hA : acc + 64 ≤ 2048) (hA8 : acc % 8 = 0)
    (hx8 : x % 8 = 0) {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (square acc x)) s0 fun s' => Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [AR acc b] s0.mem s'.mem ∧ accW acc s'.mem b 8 = V s0.mem b x * V s0.mem b x := by
  have hX : ∀ i, dw s0.mem b (x + 8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
  unfold square
  simp only [List.append_assoc]
  refine WP.append (ld4_ok (by omega) hx8 hc) fun s1 ⟨h1, hr1, hm1⟩ => ?_
  refine WP.append zero3_ok fun s2 ⟨e4, e5, e6, hr2, hm2⟩ => ?_
  have hr12 := hr1.trans (hr2.mono (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr12 (by decide)
  have hA2 : WRegs (fun i => dw s0.mem b (x + 8 * i)) s2 := fun i hi => by
    rw [hr2.gpr _ (by revert hi; revert i; decide), h1 i hi]
  refine WP.append (columns_ok (cs := sqCs fun i => dw s0.mem b (x + 8 * i))
    (Inv := fun _ => WRegs fun i => dw s0.mem b (x + 8 * i)) (col := sqCol acc)
    (fun k hk s h hi => sqCol_ok hA hA8 hX hk h hi) 8 (Nat.le_refl _) s2
    (ColInv.init hc2 hr12 (by rw [hm2, hm1]) e4 e5 e6) hA2)
    fun s3 ⟨h3, _⟩ => ?_
  have hsum := sqCols_sum fun i => dw s0.mem b (x + 8 * i)
  have hlt : val4 (fun i => dw s0.mem b (x + 8 * i)) * val4 (fun i => dw s0.mem b (x + 8 * i)) <
      (2 ^ 64) ^ 8 := by
    rw [show (8 : Nat) = 4 + 4 from rfl, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (val4_lt fun i _ => hX i) (val4_lt fun i _ => hX i)
  have hfin := h3.final (by omega)
  refine wp_li (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => ?_
  have hr5 : Rest clob64 s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  have hm5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  have hd0 : DblInv acc b s0 x (fun i => dw s3.mem b (acc + 8 * i)) 0 s5 :=
    ⟨h3.ctx.of_rest hr5 (by decide), h3.rest.trans hr5, by rw [hm5]; exact h3.frame,
      fun i _ _ => by rw [hm5], by rw [u5.other _ (by decide), u4.gpr]; rfl, fun h' => absurd h' (by decide),
      by rw [u5.gpr]; decide, by rw [u5.gpr]; rfl⟩
  refine WP.mono (dbls_ok hx hA hA8 hx8 (fun i => dw_lt _ _ _) 8 (Nat.le_refl _) s5 hd0) fun s6 h6 =>
    ⟨h6.ctx, h6.rest, h6.frame, ?_⟩
  have hv := h6.val
  rw [colsV_add, colsV_dq] at hv
  have hd := colsV_dbw (C := fun i => dw s3.mem b (acc + 8 * i)) (fun i => dw_lt _ _ _) 7
  rw [← accW_eq, hfin] at hd
  rw [V_eq4]
  have := accW_lt (acc := acc) s6.mem b 8
  generalize (2 ^ 64) ^ 8 = K at *
  generalize accW acc s6.mem b 8 = A at *
  generalize val4 (fun i => dw s0.mem b (x + 8 * i)) * val4 (fun i => dw s0.mem b (x + 8 * i)) = Q at *
  generalize colsV (dbw fun i => dw s3.mem b (acc + 8 * i)) 8 = D at *
  generalize colsV (sqCs fun i => dw s0.mem b (x + 8 * i)) 8 = S at *
  generalize dsq (fun i => dw s0.mem b (x + 8 * i)) = E at *
  generalize (s6.gpr .a4).toNat = c at *
  generalize dw s3.mem b (acc + 8 * 7) / 2 ^ 63 = t at *
  rcases Nat.eq_zero_or_pos (c + t) with h0 | hpos
  · have : c = 0 := by omega
    have : t = 0 := by omega
    subst_vars; omega
  · have : K ≤ K * (c + t) := Nat.le_mul_of_pos_right _ hpos
    rw [Nat.mul_add] at this
    omega

end

end VG.Proof.X25519.RISCV64.R64
