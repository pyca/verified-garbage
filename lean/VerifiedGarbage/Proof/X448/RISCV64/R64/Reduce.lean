module

public import VerifiedGarbage.Proof.X448.RISCV64.R64.Carry
import VerifiedGarbage.Proof.X448.Limbs32
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic

/-! ### `X448.RISCV64.R64.Product`, which this module and modules that import it used -/

section

/-!
# X448 on RISC-V, 64-bit limbs: the columns of a product

The columns of `product` and `square` (the cross products): a column adds
into the accumulator `rr k, rr (k + 1), rr (k + 2)`, and its end stores the
accumulator's low word at `ACC + 8k` (`colEnd_ok`), so that after `k`
columns the words below `ACC + 8k` and the accumulator hold the sum of the
first `k` columns (`ColInv`, by induction on the columns: `columns_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.X448.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (ACC)

theorem ACC_eq : ACC = 952 := rfl

/-- The registers of the accumulators are distinct from each other and from
`a7` and `t0`. -/
theorem rr_ne : ∀ k < 14, rr k ≠ rr (k + 1) ∧ rr k ≠ rr (k + 2) ∧ rr (k + 1) ≠ rr (k + 2) ∧
    rr k ≠ .a7 ∧ rr k ≠ .t0 ∧ rr (k + 1) ≠ .a7 ∧ rr (k + 1) ≠ .t0 ∧ rr (k + 2) ≠ .a7 ∧
    rr (k + 2) ≠ .t0 ∧ rr (k + 3) = rr k := by decide

theorem rr_mem : ∀ k < 14, rr k ∈ clob64 := by decide

theorem rr_cases {k : Nat} : rr k = .a4 ∨ rr k = .a5 ∨ rr k = .a6 := by
  unfold rr RR
  rcases (by omega_using [] : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;> simp [h]

theorem rr_clob (k : Nat) : rr k ∈ clob64 := by
  unfold rr RR
  rcases (by omega_using [] : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;> simp [h]

theorem Keeps.rest {rs : List Reg} {s s' : State} (h : Keeps rs s s') : Rest rs s s' :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The words below `ACC + 8k`. -/
def accW (m : Mem) (b : Addr) : Nat → Nat
  | 0 => 0
  | k + 1 => accW m b k + (2 ^ 64) ^ k * dw m b (ACC + 8 * k)

theorem accW_lt (m : Mem) (b : Addr) : ∀ k, accW m b k < (2 ^ 64) ^ k
  | 0 => by simp [accW]
  | k + 1 => by
    have := accW_lt m b k
    have := dw_lt m b (ACC + 8 * k)
    rw [accW, Nat.pow_succ (n := 2 ^ 64)]
    calc accW m b k + (2 ^ 64) ^ k * dw m b (ACC + 8 * k)
        < (2 ^ 64) ^ k + (2 ^ 64) ^ k * dw m b (ACC + 8 * k) := by omega_arith
      _ = (2 ^ 64) ^ k * (dw m b (ACC + 8 * k) + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ (2 ^ 64) ^ k * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega_using [this])

theorem accW_congr {m m' : Mem} {b : Addr} : ∀ {k}, (∀ c < k, dw m' b (ACC + 8 * c) = dw m b (ACC + 8 * c)) →
    accW m' b k = accW m b k
  | 0, _ => rfl
  | k + 1, h => by
    rw [accW, accW, accW_congr (fun c hc => h c (by omega_using [hc])), h k (by omega_using [])]

/-- The sum of a list of terms, given by a function. -/
def tsum (f : Nat × Nat → Nat) (ps : List (Nat × Nat)) : Nat := (ps.map f).sum

theorem tsum_cons (f : Nat × Nat → Nat) (p : Nat × Nat) (ps : List (Nat × Nat)) :
    tsum f (p :: ps) = f p + tsum f ps := by simp [tsum]

theorem tsum_le {f : Nat × Nat → Nat} {B : Nat} :
    ∀ {ps : List (Nat × Nat)}, (∀ p ∈ ps, f p ≤ B) → tsum f ps ≤ ps.length * B
  | [], _ => by simp [tsum]
  | p :: ps, h => by
    rw [tsum_cons, List.length_cons, Nat.succ_mul]
    have := h p (List.mem_cons_self ..)
    have := tsum_le (ps := ps) fun q hq => h q (List.mem_cons_of_mem _ hq)
    omega_arith

/-- The sum of the first `k` columns. -/
def colsV (cs : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => colsV cs k + (2 ^ 64) ^ k * cs k

theorem accW_eq (m : Mem) (b : Addr) : ∀ k, accW m b k = colsV (fun c => dw m b (ACC + 8 * c)) k
  | 0 => rfl
  | k + 1 => by rw [accW, colsV, accW_eq m b k]

section
variable {b : Addr}

/-- After `k` columns, from `s0`: the words below `ACC + 8k` and the
accumulator `rr k, rr (k + 1)` (with `rr (k + 2)` zero) hold the sum of the
first `k` columns `cs`; the code changed only `clob64` and `ACC`. -/
structure ColInv (b : Addr) (s0 : State) (cs : Nat → Nat) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem
  top : s.gpr (rr (k + 2)) = 0
  val : accW s.mem b k + (2 ^ 64) ^ k * ((s.gpr (rr k)).toNat + 2 ^ 64 * (s.gpr (rr (k + 1))).toNat) =
    colsV cs k

/-- The end of column `k`: the low word stored, the register zeroed. -/
theorem colEnd_ok {s0 : State} {k : Nat} (hk : k < 14) {s : State} (hc : Ctx b s)
    (hr : Rest clob64 s0 s) (hf : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem)
    {cs : Nat → Nat}
    (hv : accW s.mem b k + (2 ^ 64) ^ k * val3 s (rr k) (rr (k + 1)) (rr (k + 2)) = colsV cs (k + 1)) :
    WP isa (.block (colEnd k)) s fun s' => ColInv b s0 cs (k + 1) s' ∧
      ∀ r, r ≠ rr k → s'.gpr r = s.gpr r := by
  obtain ⟨h01, h02, h12, h07, h00, h17, h10, h27, h20, h3⟩ := rr_ne k hk
  have hA := ACC_eq
  unfold colEnd
  refine sd_ok hc (by omega_using [hk, hA]) (by omega_using [hA]) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ?_
  have hm : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (ACC + 8 * k)) (s.gpr (rr k)) := by
    rw [u2.mem, u1.mem]
  have hrr : rr k ∈ clob64 := rr_mem k hk
  have hr2 : Rest clob64 s s2 := (u1.rest _).trans (u2.rest (ws := clob64) hrr)
  refine ⟨⟨hc.of_rest hr2 (by decide), hr.trans hr2, ?_, ?_, ?_⟩,
    fun r hr' => by rw [u2.other _ hr', u1.gpr]⟩
  · rw [hm]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains b (by omega_using []) (by omega_using [hk]) (by omega_using [hA]))
  · rw [show k + 1 + 2 = k + 3 by omega_using [], h3, u2.gpr]; rfl
  · have e1 : s2.gpr (rr (k + 1)) = s.gpr (rr (k + 1)) := by rw [u2.other _ (Ne.symm h01), u1.gpr]
    have e2 : s2.gpr (rr (k + 1 + 1)) = s.gpr (rr (k + 2)) := by
      rw [show k + 1 + 1 = k + 2 by omega_using [], u2.other _ (Ne.symm h02), u1.gpr]
    have ea : accW s2.mem b k = accW s.mem b k := accW_congr fun c hc' => by
      rw [hm, dw_write_other _ _ _ (by omega_using [hc']) (by omega_using [hk, hA, hc']) (by omega_using [hk, hA])]
    have ek : dw s2.mem b (ACC + 8 * k) = (s.gpr (rr k)).toNat := by rw [hm, dw_write_self]
    rw [accW, ea, ek, e1, e2, ← hv, val3]
    rw [Nat.pow_succ (n := 2 ^ 64)]
    generalize (2 ^ 64) ^ k = K
    generalize (s.gpr (rr k)).toNat = a
    generalize (s.gpr (rr (k + 1))).toNat = c
    generalize (s.gpr (rr (k + 2))).toNat = d
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by decide]
    generalize 2 ^ 64 = W
    grind

theorem w_ne : ∀ i < 7, ∀ j < 7, i ≠ j → w i ≠ w j := by decide

theorem w_clob : ∀ i < 7, w i ∈ clob64 := by decide

/-- `w 0`, …, `w (n - 1)` loaded from `[o]`. -/
theorem lds_ok {o : Nat} (ho : o + 56 ≤ 2048) (ho8 : o % 8 = 0) :
    ∀ n ≤ 7, ∀ s, Ctx b s →
      WP isa (.block ((List.range n).map fun i => .load .d (w i) .a3 (o + 8 * i))) s fun s' =>
        (∀ i < n, (s'.gpr (w i)).toNat = dw s.mem b (o + 8 * i)) ∧ Rest clob64 s s' ∧
        s'.mem = s.mem
  | 0, _, s, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, rfl⟩
  | n + 1, hn, s, hc => by
    rw [List.range_succ, List.map_append]
    refine WP.append (lds_ok ho ho8 n (by omega_using [hn]) s hc) fun s1 ⟨h1, hr1, hm1⟩ => ?_
    refine ld_ok (hc.of_rest hr1 (by decide)) (by omega_using [ho, hn]) (by omega_using [ho8]) fun s2 u2 => WP.block_nil ?_
    refine ⟨fun i hi => ?_, hr1.trans (u2.rest (w_clob n (by omega_using [hn]))), by rw [u2.mem, hm1]⟩
    by_cases hin : i = n
    · subst hin; rw [u2.gpr, hm1]; rfl
    · rw [u2.other _ (w_ne i (by omega_using [hn, hi]) n (by omega_using [hn]) hin)]; exact h1 i (by omega_using [hi, hin])

/-- `zero3`: the accumulator of column 0 zero. -/
theorem zero3_ok {s : State} :
    WP isa (.block zero3) s fun s' => s'.gpr .a4 = 0 ∧ s'.gpr .a5 = 0 ∧ s'.gpr .a6 = 0 ∧
      Rest [.a4, .a5, .a6] s s' ∧ s'.mem = s.mem := by
  unfold zero3
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => wp_li (by decide) fun s3 u3 =>
    WP.block_nil ⟨?_, ?_, ?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
      by rw [u3.mem, u2.mem, u1.mem]⟩
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
  · rw [u3.other _ (by decide), u2.gpr]; rfl
  · rw [u3.gpr]; rfl

/-- The columns, by induction. -/
theorem columns_ok {s0 : State} {cs : Nat → Nat} {Inv : Nat → State → Prop} {col : Nat → List Instr}
    (hcol : ∀ k < 14, ∀ s, ColInv b s0 cs k s → Inv k s →
      WP isa (.block (col k)) s fun s' => ColInv b s0 cs (k + 1) s' ∧ Inv (k + 1) s') :
    ∀ n ≤ 14, ∀ s, ColInv b s0 cs 0 s → Inv 0 s →
      WP isa (.block ((List.range n).flatMap col)) s fun s' => ColInv b s0 cs n s' ∧ Inv n s'
  | 0, _, s, h, hi => WP.block_nil ⟨h, hi⟩
  | n + 1, hn, s, h, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (columns_ok hcol n (by omega_using [hn]) s h hi) fun s1 ⟨h1, hi1⟩ =>
      hcol n (by omega_using [hn]) s1 h1 hi1

/-- After the fourteen columns, the words at `ACC` are the columns' sum. -/
theorem ColInv.final {s0 : State} {cs : Nat → Nat} {s : State} (h : ColInv b s0 cs 14 s)
    (hlt : colsV cs 14 < (2 ^ 64) ^ 14) : accW s.mem b 14 = colsV cs 14 := by
  have hv := h.val
  have := accW_lt s.mem b 14
  generalize (2 ^ 64) ^ 14 = K at *
  generalize accW s.mem b 14 = A at *
  generalize (s.gpr (rr 14)).toNat + 2 ^ 64 * (s.gpr (rr (14 + 1))).toNat = C at *
  generalize colsV cs 14 = V at *
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · omega_using [hv]
  · have : K ≤ K * C := Nat.le_mul_of_pos_right _ hC
    omega_using [hlt, hv, this]

end

end VG.Proof.X448.RISCV64.R64

end

end

/-!
# X448 on RISC-V, 64-bit limbs: the reduction of a product

The product `L + 2⁴⁴⁸ H` at `ACC` (fourteen words) becomes the seven words
`T_k` of `L + H + (H - H mod 2²²⁴) + rot(H)` (`redT`), congruent to it modulo
`p` (`redT_mod`); `redStep k` computes word `k` with its carries
(`redStep_ok`, the invariant `RedInv`), and `reduce o` folds the carry out in
twice and stores the result (`reduce_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.X448.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (ACC)
open VG.Spec.X448 (P)

/-- Word `k` of `L + H + (H - H mod 2²²⁴) + rot(H)`, for the product's words `Pw`. -/
def redT (Pw : Nat → Nat) (k : Nat) : Nat :=
  Pw k + Pw (7 + k) + (if 4 ≤ k then Pw (7 + k) else 0) +
    (if k = 3 then 2 ^ 32 * (Pw 10 / 2 ^ 32) else 0) +
    (Pw (7 + (k + 3) % 7) / 2 ^ 32 + 2 ^ 32 * (Pw (7 + (k + 4) % 7) % 2 ^ 32))

/-- `2⁴⁴⁸ H ≡ H + (H - H mod 2²²⁴) + rot(H)` modulo `p`, word by word. -/
theorem redT_mod (Pw : Nat → Nat) : colsV (redT Pw) 7 % P = colsV Pw 14 % P := by
  simp only [colsV, redT, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceEqDiff,
    ↓reduceIte]
  obtain e7 := Nat.mod_add_div (Pw 7) (2 ^ 32)
  obtain e8 := Nat.mod_add_div (Pw 8) (2 ^ 32)
  obtain e9 := Nat.mod_add_div (Pw 9) (2 ^ 32)
  obtain e10 := Nat.mod_add_div (Pw 10) (2 ^ 32)
  obtain e11 := Nat.mod_add_div (Pw 11) (2 ^ 32)
  obtain e12 := Nat.mod_add_div (Pw 12) (2 ^ 32)
  obtain e13 := Nat.mod_add_div (Pw 13) (2 ^ 32)
  generalize Pw 7 % 2 ^ 32 = l0 at *
  generalize Pw 8 % 2 ^ 32 = l1 at *
  generalize Pw 9 % 2 ^ 32 = l2 at *
  generalize Pw 10 % 2 ^ 32 = l3 at *
  generalize Pw 11 % 2 ^ 32 = l4 at *
  generalize Pw 12 % 2 ^ 32 = l5 at *
  generalize Pw 13 % 2 ^ 32 = l6 at *
  generalize Pw 7 / 2 ^ 32 = u0 at *
  generalize Pw 8 / 2 ^ 32 = u1 at *
  generalize Pw 9 / 2 ^ 32 = u2 at *
  generalize Pw 10 / 2 ^ 32 = u3 at *
  generalize Pw 11 / 2 ^ 32 = u4 at *
  generalize Pw 12 / 2 ^ 32 = u5 at *
  generalize Pw 13 / 2 ^ 32 = u6 at *
  rw [← e7, ← e8, ← e9, ← e10, ← e11, ← e12, ← e13]
  generalize Pw 0 = p0
  generalize Pw 1 = p1
  generalize Pw 2 = p2
  generalize Pw 3 = p3
  generalize Pw 4 = p4
  generalize Pw 5 = p5
  generalize Pw 6 = p6
  obtain key : ∀ A B M : Nat, B = A + P * M → A % P = B % P := fun A B M h => by
    rw [h, Nat.add_mul_mod_self_left]
  refine key _ _ ((l0 + 2 ^ 32 * u0) + 2 ^ 64 * (l1 + 2 ^ 32 * u1) + 2 ^ 128 * (l2 + 2 ^ 32 * u2) +
      2 ^ 192 * l3 + (2 ^ 224 + 1) * (u3 + 2 ^ 32 * (l4 + 2 ^ 32 * u4) + 2 ^ 96 * (l5 + 2 ^ 32 * u5) +
        2 ^ 160 * (l6 + 2 ^ 32 * u6))) ?_
  rw [VG.Proof.X448.Limbs32.P_eq]
  omega_using []

variable {s : State}

/-- `r + v` into `r`, its carry added to `c`. -/
theorem addc_ok {r v c : Reg} (hrv : r ≠ v) (hr7 : r ≠ .a7) (hc7 : c ≠ .a7) (hcr : c ≠ r) :
    WP isa (.block [.add r r v, .sltu .a7 r v, .add c c .a7]) s fun s' =>
      ((s.gpr c).toNat < 2 ^ 63 → (s'.gpr r).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr r).toNat + (s.gpr v).toNat + 2 ^ 64 * (s.gpr c).toNat) ∧ Keeps [r, .a7, c] s s' := by
  rw [show ([.add r r v, .sltu .a7 r v, .add c c .a7] : List Instr) =
    [.add r r v, .sltu .a7 r v] ++ [.add c c .a7] from rfl]
  refine WP.append (addOut_ok hrv hr7) fun s1 ⟨e1, k1⟩ => WP.mono addSmall_ok fun s2 ⟨e2, k2⟩ =>
    ⟨fun hc => ?_, (k1.trans k2).mono fun x hx => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with (h | h) | h <;> simp only [h, true_or, or_true]⟩
  obtain hc1 : s1.gpr c = s.gpr c := k1.1 _ (by simp [hcr, hc7])
  obtain hr2 : s2.gpr r = s1.gpr r := k2.1 _ (by simp [Ne.symm hcr])
  have := (s1.gpr r).isLt
  obtain h7 : (s1.gpr .a7).toNat ≤ 1 := by have := (s.gpr r).isLt; have := (s.gpr v).isLt; omega_using [e1]
  rw [hc1] at e2
  rw [hr2, e2 (by omega_using [e1, hc])]
  omega_using [e1]

/-- The carry into word `k` of the reduction (none for word 0). -/
def cv (k : Nat) (s : State) : Nat := if k = 0 then 0 else (s.gpr (cr (k + 1))).toNat

/-- The words in `w 0`, `w 1`, …. -/
abbrev regsV (s : State) : Nat → Nat := fun c => (s.gpr (w c)).toNat

/-- Before word `k` of the reduction, from `sp` (the product at `ACC`): the
words below `k` and the carry the first `k` words of `redT`. -/
structure RedInv (b : Addr) (sp : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 sp s
  mem : s.mem = sp.mem
  val : colsV (regsV s) k + (2 ^ 64) ^ k * cv k s =
    colsV (redT fun i => dw sp.mem b (ACC + 8 * i)) k
  cy : cv k s ≤ 4

theorem red_regs : ∀ k < 7, w k ≠ .a7 ∧ w k ≠ .t0 ∧ cr k ≠ .a7 ∧ cr k ≠ .t0 ∧ cr k ≠ w k ∧
    cr (k + 1) ≠ w k ∧ cr (k + 1) ≠ cr k ∧ cr (k + 1) ≠ .a7 ∧ cr (k + 1) ≠ .t0 ∧ cr (k + 2) = cr k ∧
    w k ∈ clob64 ∧ cr k ∈ clob64 := by decide

theorem red_below' : ∀ k ∈ List.range 7, ∀ c ∈ List.range k,
    w c ≠ w k ∧ w c ≠ cr k ∧ w c ≠ .a7 ∧ w c ≠ .t0 := by decide

theorem red_below {k c : Nat} (hk : k < 7) (hc : c < k) :
    w c ≠ w k ∧ w c ≠ cr k ∧ w c ≠ .a7 ∧ w c ≠ .t0 :=
  red_below' k (List.mem_range.mpr hk) c (List.mem_range.mpr hc)

/-- What the middle of word `k` adds: `H_k` again for `k ≥ 4`, `H₃`'s upper half for `k = 3`. -/
def hmv (k h : Nat) : Nat := (if 4 ≤ k then h else 0) + (if k = 3 then 2 ^ 32 * (h / 2 ^ 32) else 0)

theorem mid_ok {k : Nat} (hk : k < 7) :
    WP isa (.block ((if 4 ≤ k then [.add (w k) (w k) .a7, .sltu .a7 (w k) .a7, .add (cr k) (cr k) .a7]
        else []) ++
      (if k = 3 then [.shift .srl .d .a7 .a7 32, .shift .sll .d .a7 .a7 32, .add (w k) (w k) .a7,
        .sltu .a7 (w k) .a7, .add (cr k) (cr k) .a7] else []))) s fun s' =>
      ((s.gpr (cr k)).toNat < 2 ^ 62 →
        (s'.gpr (w k)).toNat + 2 ^ 64 * (s'.gpr (cr k)).toNat =
          (s.gpr (w k)).toNat + 2 ^ 64 * (s.gpr (cr k)).toNat + hmv k (s.gpr .a7).toNat) ∧
      Keeps [w k, .a7, cr k] s s' := by
  obtain ⟨h7, h0, c7, c0, cw, -⟩ := red_regs k hk
  by_cases h4 : 4 ≤ k
  · rw [ite_eq_left h4, ite_eq_right (show ¬k = 3 by omega_using [h4]), List.append_nil]
    refine WP.mono (addc_ok (Ne.symm h7 |>.symm) h7 c7 cw) fun s' ⟨e, k'⟩ => ⟨fun hc => ?_, k'⟩
    rw [e (by omega_using [hc]), hmv, ite_eq_left h4, ite_eq_right (show ¬k = 3 by omega_using [h4])]; omega_using []
  · rw [ite_eq_right h4, List.nil_append]
    by_cases h3 : k = 3
    · subst h3
      rw [ite_eq_left rfl]
      refine wp_srl (by decide) fun s1 u1 => wp_sll (by decide) fun s2 u2 => ?_
      refine WP.mono (addc_ok (by decide) (by decide) (by decide) (by decide)) fun s' ⟨e, k'⟩ =>
        ⟨fun hc => ?_, ((Keeps.rest_mono_of_upd u1).trans ((Keeps.rest_mono_of_upd u2).trans k')).mono
          (by decide)⟩
      obtain ew : s2.gpr (w 3) = s.gpr (w 3) := by rw [u2.other _ (by decide), u1.other _ (by decide)]
      obtain ec : s2.gpr (cr 3) = s.gpr (cr 3) := by rw [u2.other _ (by decide), u1.other _ (by decide)]
      obtain e7 : (s2.gpr .a7).toNat = 2 ^ 32 * ((s.gpr .a7).toNat / 2 ^ 32) := by
        rw [u2.gpr, u1.gpr, toNat_shl, toNat_shr]
        have := (s.gpr .a7).isLt
        omega_using []
      rw [ec] at e
      rw [e (by omega_using [hc]), ew, e7, hmv]
      simp only [h4, ite_false, ite_true, Nat.zero_add]
      omega_using []
    · rw [ite_eq_right h3]
      refine WP.block_nil ⟨fun _ => ?_, Keeps.refl _ _⟩
      simp [hmv, h4, h3]

theorem colsV_congr {f g : Nat → Nat} : ∀ {k}, (∀ c < k, f c = g c) → colsV f k = colsV g k
  | 0, _ => rfl
  | k + 1, h => by rw [colsV, colsV, colsV_congr fun c hc => h c (by omega_using [hc]), h k (by omega_using [])]

theorem hmv_eq (Pw : Nat → Nat) (k : Nat) :
    hmv k (Pw (7 + k)) = (if 4 ≤ k then Pw (7 + k) else 0) +
      (if k = 3 then 2 ^ 32 * (Pw 10 / 2 ^ 32) else 0) := by
  unfold hmv
  by_cases h3 : k = 3
  · subst h3; rfl
  · simp only [h3, ite_false]

section
variable {b : Addr}


/-- The end of word `k`: its value and carry make the invariant for `k + 1`. -/
theorem redFinish {sp : State} {k : Nat} (hk : k < 7) {s s' : State} (h : RedInv b sp k s)
    (hkp : Keeps [w k, .a7, .t0, cr k] s s')
    (hv : (s'.gpr (w k)).toNat + 2 ^ 64 * (s'.gpr (cr k)).toNat =
      redT (fun i => dw sp.mem b (ACC + 8 * i)) k + cv k s) :
    RedInv b sp (k + 1) s' := by
  obtain ⟨h7, h0, c7, c0, cw, dw', dc, d7, d0, c2, wc, cc⟩ := red_regs k hk
  obtain hr : Rest clob64 s s' := Rest.mono (Keeps.rest hkp) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [wc, by decide, by decide, cc]
  obtain hwc : ∀ c < k, s'.gpr (w c) = s.gpr (w c) := fun c hc => by
    obtain ⟨n1, n2, n3, n4⟩ := red_below hk hc
    exact hkp.1 _ (by simp [n1, n2, n3, n4])
  obtain hcv : cv (k + 1) s' = (s'.gpr (cr k)).toNat := by
    simp only [cv, show k + 1 ≠ 0 by omega_using [], ite_false, show k + 1 + 1 = k + 2 by omega_using [], c2]
  obtain hb := (s'.gpr (w k)).isLt
  obtain hT : redT (fun i => dw sp.mem b (ACC + 8 * i)) k < 4 * 2 ^ 64 := by
    obtain l := fun j => dw_lt sp.mem b (ACC + 8 * j)
    have := l k; have := l (7 + k); have := l 10
    have := l (7 + (k + 3) % 7); have := l (7 + (k + 4) % 7)
    simp only [redT]
    split <;> split <;> omega
  have hcy := h.cy
  refine ⟨h.ctx.of_rest hr (by decide), h.rest.trans hr, by rw [hkp.2.1, h.mem], ?_, ?_⟩
  · rw [hcv, colsV, colsV, colsV_congr (g := regsV s) fun c hc => by simp only [regsV, hwc c hc],
      ← h.val, Nat.pow_succ (n := 2 ^ 64)]
    simp only [regsV] at hv ⊢
    generalize (2 ^ 64) ^ k = K
    generalize colsV (fun c => (s.gpr (w c)).toNat) k = A
    generalize (s'.gpr (w k)).toNat = a at hv
    generalize (s'.gpr (cr k)).toNat = c at hv
    generalize cv k s = d at hv
    generalize redT (fun i => dw sp.mem b (ACC + 8 * i)) k = t at hv
    have : K * a + K * 2 ^ 64 * c = K * (t + d) := by rw [Nat.mul_assoc, ← Nat.mul_add, hv]
    rw [Nat.mul_add] at this
    omega_using [this]
  · rw [hcv]; omega_using [hv, hT, hcy]

theorem redStep_ok {sp : State} {k : Nat} (hk : k < 7) (h : RedInv b sp k s) :
    WP isa (.block (redStep k (cr (k + 1)) (cr k))) s (RedInv b sp (k + 1)) := by
  have hA := ACC_eq
  obtain ⟨h7, h0, c7, c0, cw, dw', dc, d7, d0, c2, wc, cc⟩ := red_regs k hk
  have hc := h.ctx
  obtain e : redStep k (cr (k + 1)) (cr k) = .load .d (w k) .a3 (ACC + 8 * k) ::
      .load .d .a7 .a3 (ACC + 56 + 8 * k) :: ([.add (w k) (w k) .a7, .sltu (cr k) (w k) .a7] ++
      (((if 4 ≤ k then [.add (w k) (w k) .a7, .sltu .a7 (w k) .a7, .add (cr k) (cr k) .a7] else []) ++
        (if k = 3 then [.shift .srl .d .a7 .a7 32, .shift .sll .d .a7 .a7 32, .add (w k) (w k) .a7,
          .sltu .a7 (w k) .a7, .add (cr k) (cr k) .a7] else [])) ++
      (.load .d .a7 .a3 (ACC + 56 + 8 * ((k + 3) % 7)) :: .shift .srl .d .a7 .a7 32 ::
        .load .d .t0 .a3 (ACC + 56 + 8 * ((k + 4) % 7)) :: .shift .sll .d .t0 .t0 32 ::
        .logic .or .a7 .a7 .t0 :: ([.add (w k) (w k) .a7, .sltu .a7 (w k) .a7, .add (cr k) (cr k) .a7] ++
        (if 0 < k then [.add (w k) (w k) (cr (k + 1)), .sltu .a7 (w k) (cr (k + 1)),
          .add (cr k) (cr k) .a7] else []))))) := by
    simp only [redStep, List.cons_append, List.nil_append, List.append_assoc]
  rw [e]
  obtain hPw : ∀ j, j < 14 → ∀ (t : State), t.mem = sp.mem →
      (t.mem.readW (b + BitVec.ofNat 64 (ACC + 8 * j)) 64).toNat = dw sp.mem b (ACC + 8 * j) :=
    fun _ _ t ht => by rw [ht]; rfl
  refine ld_ok hc (by omega_using [hk, hA]) (by omega_using [hA]) fun s1 u1 => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest (u1.rest wc) (by decide)
  refine ld_ok hc1 (by omega_using [hk, hA]) (by omega_using [hA]) fun s2 u2 => ?_
  obtain hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := clob64) (by decide)) (by decide)
  refine WP.append (addOut_ok h7 (Ne.symm cw)) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.append (mid_ok hk) fun s4 ⟨e4, k4⟩ => ?_
  obtain m3 : ∀ r ∈ [w k, .a7, cr k], r ∈ clob64 := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [wc, by decide, cc]
  obtain m2 : ∀ r ∈ [w k, cr k], r ∈ clob64 := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [wc, cc]
  obtain hr4 : Rest clob64 s s4 := (u1.rest wc).trans ((u2.rest (by decide)).trans
    ((Rest.mono (Keeps.rest k3) m2).trans (Rest.mono (Keeps.rest k4) m3)))
  obtain hm4 : s4.mem = sp.mem := by rw [k4.2.1, k3.2.1, u2.mem, u1.mem, h.mem]
  obtain hc4 : Ctx b s4 := hc.of_rest hr4 (by decide)
  refine ld_ok hc4 (by omega_using [hA]) (by omega_using [hA]) fun s5 u5 => wp_srl (by decide) fun s6 u6 => ?_
  obtain hc6 : Ctx b s6 := hc4.of_rest ((u5.rest (ws := clob64) (by decide)).trans
    (u6.rest (by decide))) (by decide)
  refine ld_ok hc6 (by omega_using [hA]) (by omega_using [hA]) fun s7 u7 => wp_sll (by decide) fun s8 u8 =>
    wp_or fun s9 u9 => ?_
  refine WP.append (addc_ok h7 h7 c7 cw) fun s10 ⟨e10, k10⟩ => ?_
  -- the values so far
  obtain v1 : (s1.gpr (w k)).toNat = dw sp.mem b (ACC + 8 * k) := by
    rw [u1.gpr]; exact hPw k (by omega_using [hk]) s h.mem
  obtain v2 : (s2.gpr .a7).toNat = dw sp.mem b (ACC + 8 * (7 + k)) := by
    rw [u2.gpr, show ACC + 56 + 8 * k = ACC + 8 * (7 + k) by omega_using []]
    exact hPw _ (by omega_using [hk]) s1 (by rw [u1.mem, h.mem])
  rw [u2.other _ h7, v1, v2] at e3
  obtain a3 : s3.gpr .a7 = s2.gpr .a7 := k3.1 _ (by simp [Ne.symm h7, Ne.symm c7])
  obtain co2 : s2.gpr (cr k) = s1.gpr (cr k) := u2.other _ c7
  rw [a3, v2] at e4
  obtain e4 := e4 (by have := (s3.gpr (w k)).isLt; omega_using [e3, v1, v2])
  obtain v5 : (s5.gpr .a7).toNat = dw sp.mem b (ACC + 8 * (7 + (k + 3) % 7)) := by
    rw [u5.gpr, show ACC + 56 + 8 * ((k + 3) % 7) = ACC + 8 * (7 + (k + 3) % 7) by omega_using []]
    exact hPw _ (by omega_using []) s4 hm4
  obtain v7 : (s7.gpr .t0).toNat = dw sp.mem b (ACC + 8 * (7 + (k + 4) % 7)) := by
    rw [u7.gpr, show ACC + 56 + 8 * ((k + 4) % 7) = ACC + 8 * (7 + (k + 4) % 7) by omega_using []]
    exact hPw _ (by omega_using []) s6 (by rw [u6.mem, u5.mem, hm4])
  obtain v9 : (s9.gpr .a7).toNat = dw sp.mem b (ACC + 8 * (7 + (k + 3) % 7)) / 2 ^ 32 +
      2 ^ 32 * (dw sp.mem b (ACC + 8 * (7 + (k + 4) % 7)) % 2 ^ 32) := by
    rw [u9.gpr, u8.gpr, u8.other _ (by decide), u7.other _ (by decide), u6.gpr, rot_or, ← v7, ← v5]
  obtain w9 : s9.gpr (w k) = s4.gpr (w k) := by
    rw [u9.other _ h7, u8.other _ h0, u7.other _ h0, u6.other _ h7, u5.other _ h7]
  obtain c9 : s9.gpr (cr k) = s4.gpr (cr k) := by
    rw [u9.other _ c7, u8.other _ c0, u7.other _ c0, u6.other _ c7, u5.other _ c7]
  rw [w9, c9, v9] at e10
  obtain hmb : hmv k (dw sp.mem b (ACC + 8 * (7 + k))) < 2 ^ 64 := by
    have := dw_lt sp.mem b (ACC + 8 * (7 + k))
    unfold hmv; split <;> split <;> omega
  obtain hco4 : (s4.gpr (cr k)).toNat ≤ 2 := by
    have := (s4.gpr (w k)).isLt; have := (s3.gpr (w k)).isLt
    have := dw_lt sp.mem b (ACC + 8 * k); have := dw_lt sp.mem b (ACC + 8 * (7 + k))
    omega_arith
  obtain e10 := e10 (by omega_using [hco4])
  obtain kp10 : Keeps [w k, .a7, .t0, cr k] s s10 := by
    have := ((((((((((Keeps.rest_mono_of_upd u1).trans (Keeps.rest_mono_of_upd u2)).trans k3).trans
      k4).trans (Keeps.rest_mono_of_upd u5)).trans (Keeps.rest_mono_of_upd u6)).trans
      (Keeps.rest_mono_of_upd u7)).trans (Keeps.rest_mono_of_upd u8)).trans
      (Keeps.rest_mono_of_upd u9)).trans k10)
    refine this.mono fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    grind
  obtain hT := hmv_eq (fun i => dw sp.mem b (ACC + 8 * i)) k
  rw [hT] at e4
  by_cases k0 : k = 0
  · subst k0
    rw [ite_eq_right (Nat.lt_irrefl 0)]
    refine WP.block_nil (redFinish hk h kp10 ?_)
    simp only [cv, redT, Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte] at e4 ⊢
    omega_arith
  · rw [ite_eq_left (Nat.pos_of_ne_zero k0)]
    refine WP.mono (addc_ok (Ne.symm dw') h7 c7 cw) fun s11 ⟨e11, k11⟩ => redFinish hk h
      ((kp10.trans k11).mono fun r hr => ?_) ?_
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      grind
    · have ci : s10.gpr (cr (k + 1)) = s.gpr (cr (k + 1)) := kp10.1 _ (by simp [dw', d7, d0, dc])
      rw [ci] at e11
      have hcy := h.cy
      simp only [cv, k0, ite_false] at hcy ⊢
      obtain hco10 : (s10.gpr (cr k)).toNat ≤ 3 := by
        have := (s10.gpr (w k)).isLt; have := (s4.gpr (w k)).isLt
        have := dw_lt sp.mem b (ACC + 8 * (7 + (k + 3) % 7))
        omega_arith
      obtain e11 := e11 (by omega_using [hco10])
      simp only [redT]
      omega_using [e3, e4, e10, e11]

theorem reds_ok {sp : State} : ∀ n ≤ 7, ∀ s, RedInv b sp 0 s →
    WP isa (.block ((List.range n).flatMap fun k => redStep k (cr (k + 1)) (cr k))) s (RedInv b sp n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (reds_ok n (by omega_using [hn]) s h) fun s1 h1 => redStep_ok (by omega_using [hn]) h1

/-- `w 0`, …, `w (n - 1)` stored at `[o]`. -/
theorem sts_ok {o : Nat} (ho : o + 56 ≤ 2048) (ho8 : o % 8 = 0) :
    ∀ n ≤ 7, ∀ s, Ctx b s →
      WP isa (.block ((List.range n).map fun i => .store .d (w i) .a3 (o + 8 * i))) s fun s' =>
        (∀ i < n, dw s'.mem b (o + 8 * i) = (s.gpr (w i)).toNat) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem
  | 0, _, s, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn, s, hc => by
    rw [List.range_succ, List.map_append]
    refine WP.append (sts_ok ho ho8 n (by omega_using [hn]) s hc) fun s1 ⟨h1, g1, r1, w1, p1, f1⟩ => ?_
    obtain hc1 : Ctx b s1 := ⟨by rw [g1, hc.a3], hc.al, by rw [w1]; exact hc.wr⟩
    refine sd_ok hc1 (by omega_using [ho, hn]) (by omega_using [ho8]) fun s2 u2 => WP.block_nil ⟨fun i hi => ?_,
      by rw [u2.gpr, g1], by rw [u2.rd, r1], by rw [u2.wr, w1], by rw [u2.sp, p1], ?_⟩
    · rw [u2.mem]
      by_cases hin : i = n
      · subst hin; rw [dw_write_self, g1]
      · rw [dw_write_other _ _ _ (by omega_using [hin]) (by omega_using [ho, hn, hi]) (by omega_using [ho, hn])]; exact h1 i (by omega_using [hi, hin])
    · rw [u2.mem]
      exact f1.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega_using []) (by omega_using [hn]) (by omega_using [ho]))

theorem colsV7 (f : Nat → Nat) : colsV f 7 = val7 f := by
  simp only [colsV, val7]
  generalize 2 ^ 64 = B
  grind

theorem B7_eq : ((2 : Nat) ^ 64) ^ 7 = 2 ^ 224 * 2 ^ 224 := by decide

/-- Two folds of a carry `c ≤ 4` leave a number congruent to `v₁ + 2⁴⁴⁸ c`. -/
theorem fold_twice {v1 v2 v3 c c2 c3 : Nat} (hv1 : v1 < 2 ^ 224 * 2 ^ 224) (hv2 : v2 < 2 ^ 224 * 2 ^ 224)
    (hv3 : v3 < 2 ^ 224 * 2 ^ 224) (hc : c ≤ 4)
    (e2 : v2 + 2 ^ 224 * 2 ^ 224 * c2 = v1 + c + 2 ^ 224 * c)
    (e3 : v3 + 2 ^ 224 * 2 ^ 224 * c3 = v2 + c2 + 2 ^ 224 * c2) :
    v3 % P = (v1 + 2 ^ 224 * 2 ^ 224 * c) % P := by
  obtain hc2 : c2 ≤ 1 := by omega
  obtain hc3 : c3 = 0 := by omega
  subst hc3
  rw [VG.Proof.X448.Limbs32.fold448, show v1 + (2 ^ 224 + 1) * c = v2 + 2 ^ 224 * 2 ^ 224 * c2 by omega,
    VG.Proof.X448.Limbs32.fold448]
  congr 1
  omega

/-- `reduce o`: the product at `ACC` reduced into `[o]`. -/
theorem reduce_ok {o : Nat} (ho : o + 56 ≤ ACC) (ho8 : o % 8 = 0) {sp : State} (hc : Ctx b sp) :
    WP isa (.block (reduce o)) sp fun s' => Ctx b s' ∧ Rest clob64 sp s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 56⟩] sp.mem s'.mem ∧
      Proof.X448.RISCV64.V s'.mem b o % P = accW sp.mem b 14 % P := by
  have hA := ACC_eq
  unfold reduce
  simp only [List.append_assoc]
  obtain h0 : RedInv b sp 0 sp := ⟨hc, Rest.refl _ _, rfl, by simp [colsV, cv], by simp [cv]⟩
  refine WP.append (reds_ok 7 (Nat.le_refl _) sp h0) fun s1 h1 => ?_
  have hcv : cv 7 s1 = (s1.gpr .a5).toNat := rfl
  have hv1 := h1.val
  rw [hcv, colsV7] at hv1
  have hcy := h1.cy
  rw [hcv] at hcy
  refine WP.append foldR_ok fun s2 ⟨e2, k2⟩ => ?_
  obtain e2 := e2 (by omega_using [hcy])
  refine WP.append foldR_ok fun s3 ⟨e3, k3⟩ => ?_
  obtain hc2 : (s2.gpr .a5).toNat ≤ 1 := by
    have := val7_lt (f := fun i => (s1.gpr (w i)).toNat) fun i _ => (s1.gpr (w i)).isLt
    have := val7_lt (f := fun i => (s2.gpr (w i)).toNat) fun i _ => (s2.gpr (w i)).isLt
    simp only [rw7] at e2
    omega_arith
  obtain e3 := e3 (by omega_using [hc2])
  obtain hr3 : Rest clob64 sp s3 := h1.rest.trans (Rest.mono (Keeps.rest (k2.trans k3)) (by decide))
  obtain hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  obtain hm3 : s3.mem = sp.mem := by rw [k3.2.1, k2.2.1, h1.mem]
  refine WP.mono (sts_ok (by omega_using [ho, hA]) ho8 7 (Nat.le_refl _) s3 hc3) fun s4 ⟨h4, g4, r4, w4, p4, f4⟩ =>
    ⟨⟨by rw [g4, hc3.a3], hc3.al, by rw [w4]; exact hc3.wr⟩, hr3.trans ⟨fun r _ => by rw [g4], r4, w4, p4⟩,
      by rw [← hm3]; exact f4, ?_⟩
  obtain hV : Proof.X448.RISCV64.V s4.mem b o = rw7 s3 := by
    rw [V_eq]; exact val7_congr fun i hi => h4 i hi
  rw [hV]
  obtain hmod := redT_mod (fun i => dw sp.mem b (ACC + 8 * i))
  rw [← accW_eq] at hmod
  rw [← hmod, ← hv1]
  have l v := val7_lt (f := fun i => (State.gpr v (w i)).toNat) fun i _ => (v.gpr (w i)).isLt
  simp only [rw7, B7_eq] at e2 e3 ⊢
  rw [B7_eq] at l
  exact fold_twice (l s1) (l s2) (l s3) hcy e2 e3

end

end VG.Proof.X448.RISCV64.R64
