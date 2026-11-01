module

import VerifiedGarbage.Proof.X448.RISCV64.R64.Macc
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic

/-!
# X448 on RISC-V, 64-bit limbs: the columns of a product

The columns of `product` and `square` (the cross products): a column's terms
add into the accumulator `rr k, rr (k + 1), rr (k + 2)` (`terms_ok`, by
induction on the terms), and its end stores the accumulator's low word at
`ACC + 8k` (`colEnd_ok`), so that after `k` columns the words below `ACC +
8k` and the accumulator hold the sum of the first `k` columns (`ColInv`).
The terms each column adds (`colSum`) are given by a function on the state
(`TermOk`), which `product` and `square` provide.
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
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;> simp [h]

theorem rr_clob (k : Nat) : rr k ∈ clob64 := by
  unfold rr RR
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;> simp [h]

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
        < (2 ^ 64) ^ k + (2 ^ 64) ^ k * dw m b (ACC + 8 * k) := by omega
      _ = (2 ^ 64) ^ k * (dw m b (ACC + 8 * k) + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ (2 ^ 64) ^ k * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega)

theorem accW_congr {m m' : Mem} {b : Addr} : ∀ {k}, (∀ c < k, dw m' b (ACC + 8 * c) = dw m b (ACC + 8 * c)) →
    accW m' b k = accW m b k
  | 0, _ => rfl
  | k + 1, h => by
    rw [accW, accW, accW_congr (fun c hc => h c (by omega)), h k (by omega)]

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
    omega

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
  refine sd_ok hc (by omega) (by omega) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ?_
  have hm : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (ACC + 8 * k)) (s.gpr (rr k)) := by
    rw [u2.mem, u1.mem]
  have hrr : rr k ∈ clob64 := rr_mem k hk
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
    have ea : accW s2.mem b k = accW s.mem b k := accW_congr fun c hc' => by
      rw [hm, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
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

/-- A column's terms: from a state with the accumulator `acc`, each term `p`
of `ps` adds `f p` and keeps `Inv`. -/
def TermOk (b : Addr) (s0 : State) (k : Nat) (Inv : State → Prop) (f : Nat × Nat → Nat)
    (code : Nat × Nat → List Instr) (p : Nat × Nat) : Prop :=
  ∀ s, Inv s → Ctx b s → Rest clob64 s0 s → Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem →
    WP isa (.block (code p)) s fun s' => Inv s' ∧ Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s'.mem ∧
      accW s'.mem b k = accW s.mem b k ∧
      (val3 s (rr k) (rr (k + 1)) (rr (k + 2)) + f p < 2 ^ 192 →
        val3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = val3 s (rr k) (rr (k + 1)) (rr (k + 2)) + f p)

/-- A column's terms, by induction on them. -/
theorem terms_ok {s0 : State} {k : Nat} {Inv : State → Prop} {f : Nat × Nat → Nat}
    {code : Nat × Nat → List Instr} :
    ∀ (ps : List (Nat × Nat)), (∀ p ∈ ps, TermOk b s0 k Inv f code p) → ∀ s, Inv s → Ctx b s →
      Rest clob64 s0 s → Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem →
      val3 s (rr k) (rr (k + 1)) (rr (k + 2)) + tsum f ps < 2 ^ 192 →
      WP isa (.block (ps.flatMap code)) s fun s' => Inv s' ∧ Ctx b s' ∧ Rest clob64 s0 s' ∧
        Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s'.mem ∧
        accW s'.mem b k = accW s.mem b k ∧
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
theorem column_ok {s0 : State} {k : Nat} (hk : k < 14) {Inv : State → Prop} {f : Nat × Nat → Nat}
    {code : Nat × Nat → List Instr} {cs : Nat → Nat} (ps : List (Nat × Nat))
    (hok : ∀ p ∈ ps, TermOk b s0 k Inv f code p) (hcs : cs k = tsum f ps)
    (hbd : tsum f ps < 7 * 2 ^ 128)
    (hinv : ∀ s s', Inv s → (∀ r, r ≠ rr k → s'.gpr r = s.gpr r) → Inv s') {s : State}
    (h : ColInv b s0 cs k s) (hi : Inv s) :
    WP isa (.block (ps.flatMap code ++ colEnd k)) s fun s' => ColInv b s0 cs (k + 1) s' ∧ Inv s' := by
  have hv0 : val3 s (rr k) (rr (k + 1)) (rr (k + 2)) =
      (s.gpr (rr k)).toNat + 2 ^ 64 * (s.gpr (rr (k + 1))).toNat := by
    simp only [val3, h.top]; rfl
  have hl := (s.gpr (rr k)).isLt
  have hh := (s.gpr (rr (k + 1))).isLt
  refine WP.append (terms_ok ps hok s hi h.ctx h.rest h.frame (by rw [hv0]; omega_arith))
    fun s1 ⟨hi1, hc1, hr1, hf1, ha1, hv1⟩ => ?_
  have hwp := colEnd_ok (cs := cs) hk hc1 hr1 hf1 (by
    rw [ha1, hv1, hv0, colsV, ← h.val, hcs, Nat.mul_add]; omega_arith)
  exact WP.mono hwp fun s2 ⟨h2, hk2⟩ => ⟨h2, hinv s1 s2 hi1 hk2⟩

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
    refine WP.append (lds_ok ho ho8 n (by omega) s hc) fun s1 ⟨h1, hr1, hm1⟩ => ?_
    refine ld_ok (hc.of_rest hr1 (by decide)) (by omega) (by omega) fun s2 u2 => WP.block_nil ?_
    refine ⟨fun i hi => ?_, hr1.trans (u2.rest (w_clob n (by omega))), by rw [u2.mem, hm1]⟩
    by_cases hin : i = n
    · subst hin; rw [u2.gpr, hm1]; rfl
    · rw [u2.other _ (w_ne i (by omega) n (by omega) hin)]; exact h1 i (by omega)

/-- `ld6`. -/
theorem ld6_ok {o : Nat} (ho : o + 56 ≤ 2048) (ho8 : o % 8 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (ld6 o)) s fun s' =>
      (∀ i < 6, (s'.gpr (w i)).toNat = dw s.mem b (o + 8 * i)) ∧ Rest clob64 s s' ∧ s'.mem = s.mem :=
  lds_ok ho ho8 6 (by decide) s hc

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
    exact WP.append (columns_ok hcol n (by omega) s h hi) fun s1 ⟨h1, hi1⟩ =>
      hcol n (by omega) s1 h1 hi1

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
  · omega
  · have : K ≤ K * C := Nat.le_mul_of_pos_right _ hC
    omega

end

end VG.Proof.X448.RISCV64.R64
