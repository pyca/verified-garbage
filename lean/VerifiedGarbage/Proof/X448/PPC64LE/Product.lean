module

public import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Product
public import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X448 on PPC64LE: the fourteen doublewords of a product, in registers

`mulR`'s columns (`Impl/X448/PPC64LE.lean`) leave the product of the
operands' words in `opA` and `opB` in the registers `pw 0`, …, `pw 13`
(`columns_ok`): each column `k` clears `pw (k + 2)` and adds its terms
`a_i b_j` (`i + j = k`) into the accumulator `pw k, pw (k + 1), pw (k + 2)`
(`termR_ok`, by `acc3_ok`), so that after `k` columns `pw 0`, …,
`pw (k - 1)` and the accumulator hold the sum of the first `k` (`ColS`,
`colR_ok`). From word 9 on, `pw` reuses the registers of operands' words no
later column reads (`live_facts`). Also the doublewords of a row-by-row
product of limbs at `ACC` (`accW_val32`), which Ed448's scalar arithmetic
reads.
-/

-- separate module: its proofs cost more than its imports, and its importer's changes need not
-- re-check them

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P)

/-! ## Doublewords -/

/-- `N` doublewords from `acc` are their `2N` words. -/
theorem accW_val32 (acc : Nat) (m : Mem) (b : Addr) :
    ∀ N, accW acc m b N = val32 (fun k => wd m b (acc + 4 * k)) (2 * N)
  | 0 => rfl
  | N + 1 => by
    rw [accW, accW_val32 acc m b N, show 2 * (N + 1) = 2 * N + 1 + 1 by omega, val32_succ, val32_succ,
      dw_split, show acc + 4 * (2 * N) = acc + 8 * N by omega,
      show acc + 4 * (2 * N + 1) = acc + 8 * N + 4 by omega,
      show 32 * (2 * N + 1) = 64 * N + 32 by omega, show 32 * (2 * N) = 64 * N by omega,
      Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm 64 N]
    rw [Nat.mul_add, Nat.add_assoc, ← Nat.mul_assoc, Nat.add_assoc]

/-- The doublewords from `acc`, split at `i`. -/
theorem accW_add (acc : Nat) (m : Mem) (b : Addr) (i : Nat) :
    ∀ k, accW acc m b (i + k) = accW acc m b i + (2 ^ 64) ^ i * accW (acc + 8 * i) m b k
  | 0 => by simp [accW]
  | k + 1 => by
    rw [← Nat.add_assoc, accW, accW_add acc m b i k, accW, Nat.mul_add, Nat.pow_add, Nat.mul_assoc,
      ← Nat.add_assoc acc (8 * i) (8 * k), Nat.mul_add ((2 ^ 64) ^ i), Nat.add_assoc]

/-- An element's fourteen limbs are its seven doublewords. -/
theorem V_eq_cols (m : Mem) (b : Addr) (o : Nat) : V m b o = colsV (ew m b o) 7 := by
  have h := accW_val32 o m b 7
  have e : ∀ k, accW o m b k = colsV (ew m b o) k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [accW, colsV, ih]
  rw [← e, h]; rfl

theorem colsV_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = g k) → colsV f n = colsV g n
  | 0, _ => rfl
  | n + 1, h => by rw [colsV, colsV, colsV_congr (fun k hk => h k (by omega)), h n (by omega)]

/-! ## The product in registers -/

/-- The registers `mulR` changes before it restores them. -/
abbrev clobR : List Reg :=
  [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23,
    .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem pw_inj : ∀ j < 15, ∀ k < 15, pw j = pw k → j = k := by decide

theorem pw_facts : ∀ k < 15, pw k ≠ .r4 ∧ pw k ≠ .r5 ∧ pw k ≠ .r6 ∧ pw k ∈ clobR := by decide

theorem op_facts : ∀ i < 7, opA i ≠ .r4 ∧ opA i ≠ .r5 ∧ opB i ≠ .r4 ∧ opB i ≠ .r5 := by decide

/-- The operands' words that column `k` or a later one reads (`k ≤ i + 6`)
are in none of its accumulator's registers. -/
theorem live_facts' : ∀ k < 13, ∀ i < 7, i + 6 < k ∨
    ((opA i ≠ pw k ∧ opA i ≠ pw (k + 1) ∧ opA i ≠ pw (k + 2)) ∧
    (opB i ≠ pw k ∧ opB i ≠ pw (k + 1) ∧ opB i ≠ pw (k + 2))) := by decide

theorem live_facts {k : Nat} (hk : k < 13) {i : Nat} (hi : i < 7) (hl : k ≤ i + 6) :
    (opA i ≠ pw k ∧ opA i ≠ pw (k + 1) ∧ opA i ≠ pw (k + 2)) ∧
    (opB i ≠ pw k ∧ opB i ≠ pw (k + 1) ∧ opB i ≠ pw (k + 2)) :=
  (live_facts' k hk i hi).resolve_left (by omega)

theorem pairs_ok : ∀ k < 13, ∀ p ∈ pairs k, p.1 < 7 ∧ p.2 < 7 ∧ k ≤ p.1 + 6 ∧ k ≤ p.2 + 6 := by decide

theorem pairs_len : ∀ k < 13, (pairs k).length ≤ 7 := by decide

section
variable {b : Addr}

/-- From `s0`: what the terms of column `k` keep. -/
structure TermS (s0 : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clobR s0 s
  mem : s.mem = s0.mem
  keep : ∀ r, r ≠ pw k → r ≠ pw (k + 1) → r ≠ pw (k + 2) → r ≠ .r4 → r ≠ .r5 → s.gpr r = s0.gpr r

/-- The product of the operands' words `p.1` and `p.2` in `s`. -/
def opProd (s : State) (p : Nat × Nat) : Nat := (s.gpr (opA p.1)).toNat * (s.gpr (opB p.2)).toNat

/-- A term `a_i b_j` of column `k`. -/
theorem termR_ok {s0 : State} {k : Nat} {p : Nat × Nat} (hk : k < 13)
    (hp : p.1 < 7 ∧ p.2 < 7 ∧ k ≤ p.1 + 6 ∧ k ≤ p.2 + 6) {s : State} (h : TermS (b := b) s0 k s) :
    WP isa (.block (termR k p)) s fun s' => TermS (b := b) s0 k s' ∧
      (v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + opProd s0 p < 2 ^ 192 →
        v3 s' (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + opProd s0 p) := by
  obtain ⟨hi, hj, hli, hlj⟩ := hp
  obtain ⟨p04, p05, -, p0c⟩ := pw_facts k (by omega)
  obtain ⟨p14, p15, -, p1c⟩ := pw_facts (k + 1) (by omega)
  obtain ⟨p24, p25, -, p2c⟩ := pw_facts (k + 2) (by omega)
  have h01 : pw k ≠ pw (k + 1) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
  have h02 : pw k ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
  have h12 : pw (k + 1) ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
  obtain ⟨a4, a5, -, -⟩ := op_facts p.1 hi
  obtain ⟨-, -, b4, b5⟩ := op_facts p.2 hj
  obtain ⟨⟨a0, a1, a2⟩, -⟩ := live_facts hk hi hli
  obtain ⟨-, ⟨b0, b1, b2⟩⟩ := live_facts hk hj hlj
  have ka : s.gpr (opA p.1) = s0.gpr (opA p.1) := h.keep _ a0 a1 a2 a4 a5
  have kb : s.gpr (opB p.2) = s0.gpr (opB p.2) := h.keep _ b0 b1 b2 b4 b5
  simp only [termR]
  refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => ?_
  refine acc3_ok h01 h02 h12 p05 fun s3 hv3 hg3 hm3 hrd3 hwr3 hsp3 => WP.block_nil ?_
  have hA := (s.gpr (opA p.1)).isLt
  have hB := (s.gpr (opB p.2)).isLt
  have g1a : s1.gpr (opA p.1) = s.gpr (opA p.1) := u1.other _ a4
  have g1b : s1.gpr (opB p.2) = s.gpr (opB p.2) := u1.other _ b4
  have elo : (s2.gpr .r4).toNat = opProd s0 p % 2 ^ 64 := by
    rw [u2.other _ (by decide), u1.gpr, BitVec.toNat_mul, ka, kb]; rfl
  have ehi : (s2.gpr .r5).toNat = opProd s0 p / 2 ^ 64 := by
    rw [u2.gpr, g1a, g1b, ka, kb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    · rfl
    · rw [← ka, ← kb]; exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt hA hB)
  have e : (s2.gpr .r4).toNat + 2 ^ 64 * (s2.gpr .r5).toNat = opProd s0 p := by
    rw [elo, ehi]; exact Nat.mod_add_div _ _
  have hv2 : v3 s2 (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) := by
    simp only [v3, u2.other _ p05, u2.other _ p15, u2.other _ p25, u1.other _ p04, u1.other _ p14,
      u1.other _ p24]
  have hr2 : Rest clobR s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hr3 : Rest clobR s2 s3 := ⟨fun r hr' => hg3 r (fun e => hr' (e ▸ p0c)) (fun e => hr' (e ▸ p1c))
    (fun e => hr' (e ▸ p2c)), hrd3, hwr3, hsp3⟩
  have hm : s3.mem = s.mem := by rw [hm3, u2.mem, u1.mem]
  refine ⟨⟨h.ctx.of_rest (hr2.trans hr3) (by decide), h.rest.trans (hr2.trans hr3), hm.trans h.mem,
    fun r n0 n1 n2 n4 n5 => ?_⟩, fun hb => ?_⟩
  · rw [hg3 r n0 n1 n2, u2.other _ n5, u1.other _ n4]; exact h.keep r n0 n1 n2 n4 n5
  · rw [hv3 (by rw [hv2, Nat.add_assoc, e]; exact hb), hv2, Nat.add_assoc, e]

/-- A column's terms, by induction on them. -/
theorem termsR_ok {s0 : State} {k : Nat} (hk : k < 13) :
    ∀ (ps : List (Nat × Nat)), (∀ p ∈ ps, p.1 < 7 ∧ p.2 < 7 ∧ k ≤ p.1 + 6 ∧ k ≤ p.2 + 6) →
      ∀ s, TermS (b := b) s0 k s →
      v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + tsum (opProd s0) ps < 2 ^ 192 →
      WP isa (.block (ps.flatMap (termR k))) s fun s' => TermS (b := b) s0 k s' ∧
        v3 s' (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + tsum (opProd s0) ps
  | [], _, s, h, _ => WP.block_nil ⟨h, by simp [tsum]⟩
  | p :: ps, hps, s, h, hb => by
    rw [List.flatMap_cons]
    rw [tsum_cons] at hb
    refine WP.append (termR_ok hk (hps p List.mem_cons_self) h) fun s1 ⟨h1, hv1⟩ => ?_
    have hv1 := hv1 (by omega)
    refine WP.mono (termsR_ok hk ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) s1 h1 (by omega))
      fun s2 ⟨h2, hv2⟩ => ⟨h2, ?_⟩
    rw [hv2, hv1, tsum_cons]; omega

/-- The value of the words `pw 0`, …, `pw (k - 1)`. -/
abbrev pwSum (s : State) (k : Nat) : Nat := colsV (fun j => (s.gpr (pw j)).toNat) k

/-- After `k` columns, from `s0`: the operands' words the later columns read
as they were, and `pw 0`, …, `pw (k - 1)` and the accumulator `pw k,
pw (k + 1)` the sum of the first `k` columns. -/
structure ColS (s0 : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clobR s0 s
  mem : s.mem = s0.mem
  ops : ∀ i < 7, k ≤ i + 6 → s.gpr (opA i) = s0.gpr (opA i) ∧ s.gpr (opB i) = s0.gpr (opB i)
  val : pwSum s k + (2 ^ 64) ^ k * ((s.gpr (pw k)).toNat + 2 ^ 64 * (s.gpr (pw (k + 1))).toNat) =
    colsV (fun c => tsum (opProd s0) (pairs c)) k

theorem tsum_lt7 {f : Nat × Nat → Nat} (hf : ∀ p, f p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    {ps : List (Nat × Nat)} (hl : ps.length ≤ 7) : tsum f ps < 7 * 2 ^ 128 := by
  have := tsum_le (ps := ps) fun p _ => hf p
  have : ps.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) ≤ 7 * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) :=
    Nat.mul_le_mul_right _ hl
  omega

/-- Column `k`. -/
theorem colR_ok {s0 : State} {k : Nat} (hk : k < 13) {s : State} (h : ColS (b := b) s0 k s) :
    WP isa (.block (colR k)) s (ColS (b := b) s0 (k + 1)) := by
  obtain ⟨-, -, -, p2c⟩ := pw_facts (k + 2) (by omega)
  unfold colR
  refine wp_li (by decide) fun s1 u1 => ?_
  have hr1 : Rest clobR s s1 := u1.rest p2c
  have hRT : TermS (b := b) s1 k s1 := ⟨h.ctx.of_rest hr1 (by decide), Rest.refl _ _, rfl, fun _ _ _ _ _ _ => rfl⟩
  have hops : ∀ i < 7, k ≤ i + 6 → s1.gpr (opA i) = s0.gpr (opA i) ∧ s1.gpr (opB i) = s0.gpr (opB i) :=
    fun i hi hl => by
      obtain ⟨⟨-, -, a2⟩, ⟨-, -, b2⟩⟩ := live_facts hk hi hl
      exact ⟨by rw [u1.other _ a2]; exact (h.ops i hi hl).1, by rw [u1.other _ b2]; exact (h.ops i hi hl).2⟩
  have hF : ∀ p ∈ pairs k, opProd s1 p = opProd s0 p := fun p hp => by
    obtain ⟨h1, h2, h3, h4⟩ := pairs_ok k hk p hp
    simp only [opProd, (hops _ h1 h3).1, (hops _ h2 h4).2]
  have hts : tsum (opProd s1) (pairs k) = tsum (opProd s0) (pairs k) := by
    unfold tsum; congr 1; exact List.map_congr_left hF
  have hlt : tsum (opProd s1) (pairs k) < 7 * 2 ^ 128 :=
    tsum_lt7 (fun p => Nat.mul_le_mul (by have := (s1.gpr (opA p.1)).isLt; omega)
      (by have := (s1.gpr (opB p.2)).isLt; omega)) (pairs_len k hk)
  have g2 : s1.gpr (pw (k + 2)) = 0 := u1.gpr
  have h01 : pw k ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
  have h11 : pw (k + 1) ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
  have hv0 : v3 s1 (pw k) (pw (k + 1)) (pw (k + 2)) =
      (s.gpr (pw k)).toNat + 2 ^ 64 * (s.gpr (pw (k + 1))).toNat := by
    simp only [v3, g2, u1.other _ h01, u1.other _ h11]; rfl
  have hl := (s.gpr (pw k)).isLt
  have hh := (s.gpr (pw (k + 1))).isLt
  refine WP.mono (termsR_ok hk (pairs k) (fun p hp => pairs_ok k hk p hp) s1 hRT
    (by rw [hv0]; omega_arith)) fun s2 ⟨h2, hv2⟩ => ?_
  have hlow : ∀ j < k, s2.gpr (pw j) = s.gpr (pw j) := fun j hj => by
    have n0 : pw j ≠ pw k := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
    have n1 : pw j ≠ pw (k + 1) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
    have n2 : pw j ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
    obtain ⟨j4, j5, -, -⟩ := pw_facts j (by omega)
    rw [h2.keep _ n0 n1 n2 j4 j5, u1.other _ n2]
  refine ⟨h2.ctx, h.rest.trans (hr1.trans h2.rest), h2.mem.trans (by rw [u1.mem, h.mem]),
    fun i hi hl => ?_, ?_⟩
  · obtain ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩ := live_facts hk hi (by omega)
    obtain ⟨a4, a5, b4, b5⟩ := op_facts i hi
    exact ⟨by rw [h2.keep _ a0 a1 a2 a4 a5]; exact (hops i hi (by omega)).1,
      by rw [h2.keep _ b0 b1 b2 b4 b5]; exact (hops i hi (by omega)).2⟩
  · have hv := h.val
    rw [show k + 1 + 1 = k + 2 by omega]
    simp only [pwSum, colsV]
    rw [colsV_congr (fun j hj => by rw [hlow j hj])]
    rw [← pwSum, ← hts]
    rw [hv0] at hv2
    unfold v3 at hv2
    rw [Nat.pow_succ (n := 2 ^ 64)]
    generalize (2 ^ 64) ^ k = K at *
    generalize pwSum s k = S at *
    generalize colsV (fun c => tsum (opProd s0) (pairs c)) k = C at *
    generalize tsum (opProd s1) (pairs k) = T at *
    generalize (s.gpr (pw k)).toNat = a at *
    generalize (s.gpr (pw (k + 1))).toNat = c at *
    generalize (s2.gpr (pw k)).toNat = a' at *
    generalize (s2.gpr (pw (k + 1))).toNat = c' at *
    generalize (s2.gpr (pw (k + 2))).toNat = d' at *
    generalize 2 ^ 64 = W at *
    rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, hv2, ← hv, Nat.mul_add K (a + W * c) T]
    omega

/-- The columns, by induction. -/
theorem colsR_ok {s0 : State} : ∀ n ≤ 13, ∀ s, ColS (b := b) s0 0 s →
    WP isa (.block ((List.range n).flatMap colR)) s (ColS (b := b) s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (colsR_ok n (by omega) s h) fun s1 h1 => colR_ok (by omega) h1

end

/-- The columns of a product of seven words sum to it. -/
theorem cols_mul (X Y : Nat → Nat) :
    colsV (fun c => tsum (fun p => X p.1 * Y p.2) (pairs c)) 13 = colsV X 7 * colsV Y 7 := by
  simp only [colsV]
  generalize 2 ^ 64 = B
  simp only [pairs, tsum, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  grind

theorem colsV_lt {f : Nat → Nat} (hf : ∀ i, f i < 2 ^ 64) : ∀ n, colsV f n < (2 ^ 64) ^ n
  | 0 => by simp [colsV]
  | n + 1 => by
    have := colsV_lt hf n
    have := hf n
    rw [colsV, Nat.pow_succ]
    calc colsV f n + (2 ^ 64) ^ n * f n < (2 ^ 64) ^ n + (2 ^ 64) ^ n * f n := by omega
      _ = (2 ^ 64) ^ n * (f n + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ (2 ^ 64) ^ n * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega)

section
variable {b : Addr}

/-- From `pw 0 = pw 1 = 0`: the fourteen words of the product of the
operands' words in `pw`. -/
theorem columns_ok {s0 : State} (hc : Ctx b s0) (h0 : s0.gpr (pw 0) = 0) (h1 : s0.gpr (pw 1) = 0) :
    WP isa (.block ((List.range 13).flatMap colR)) s0 fun s' => Ctx b s' ∧ Rest clobR s0 s' ∧
      s'.mem = s0.mem ∧
      pwSum s' 14 = colsV (fun i => (s0.gpr (opA i)).toNat) 7 * colsV (fun j => (s0.gpr (opB j)).toNat) 7 := by
  have hinit : ColS (b := b) s0 0 s0 := ⟨hc, Rest.refl _ _, rfl, fun _ _ _ => ⟨rfl, rfl⟩, by
    simp only [pwSum, colsV, Nat.pow_zero, Nat.one_mul, Nat.zero_add, h0, h1]; rfl⟩
  refine WP.mono (colsR_ok 13 (Nat.le_refl _) s0 hinit) fun s4 h4 => ⟨h4.ctx, h4.rest, h4.mem, ?_⟩
  have hv := h4.val
  have e : (fun c => tsum (opProd s0) (pairs c)) =
      (fun c => tsum (fun p => (s0.gpr (opA p.1)).toNat * (s0.gpr (opB p.2)).toNat) (pairs c)) := rfl
  rw [e, cols_mul (fun i => (s0.gpr (opA i)).toNat) (fun j => (s0.gpr (opB j)).toNat)] at hv
  have hlt : colsV (fun i => (s0.gpr (opA i)).toNat) 7 * colsV (fun j => (s0.gpr (opB j)).toNat) 7 <
      (2 ^ 64) ^ 14 := by
    have := colsV_lt (f := fun i => (s0.gpr (opA i)).toNat) (fun i => (s0.gpr (opA i)).isLt) 7
    have := colsV_lt (f := fun j => (s0.gpr (opB j)).toNat) (fun j => (s0.gpr (opB j)).isLt) 7
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (by assumption) (by assumption)) (by
      rw [← Nat.pow_add])
  have h14 := (s4.gpr (pw 14)).isLt
  have hp13 : pwSum s4 13 < (2 ^ 64) ^ 13 := colsV_lt (fun j => (s4.gpr (pw j)).isLt) 13
  rw [show pwSum s4 14 = pwSum s4 13 + (2 ^ 64) ^ 13 * (s4.gpr (pw 13)).toNat from rfl]
  rw [show (13 : Nat) + 1 = 14 from rfl] at hv
  generalize pwSum s4 13 = S at *
  generalize (s4.gpr (pw 13)).toNat = a at *
  generalize (s4.gpr (pw 14)).toNat = c at *
  generalize colsV (fun i => (s0.gpr (opA i)).toNat) 7 * colsV (fun j => (s0.gpr (opB j)).toNat) 7 = XY at *
  have : c = 0 := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exact h
    · exfalso
      have : (2 ^ 64) ^ 13 * (2 ^ 64 * c) ≥ (2 ^ 64) ^ 14 := by
        rw [show (2 ^ 64) ^ 14 = (2 ^ 64) ^ 13 * 2 ^ 64 * 1 by rfl, Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
      omega
  subst this
  omega

end

end VG.Proof.X448.PPC64LE
