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
# X448 on PPC64LE: the fourteen doublewords of a product

The doublewords of a product of limbs at `ACC` are its limbs
(`accW_val32`), as Ed448's scalar arithmetic reads them.

`columns_ok`: `mul`'s columns (`Impl/X448/PPC64LE.lean`) leave the product
of the operands' words in `opA` and `opB` in the registers `pw 0`, …,
`pw 13`: each column `k` clears `pw (k + 2)` and adds its terms `a_i b_j`
(`i + j = k`) into the accumulator `pw k, pw (k + 1), pw (k + 2)`
(`termR_ok`, by `acc3_ok`), so that after `k` columns `pw 0`, …, `pw (k - 1)`
and the accumulator hold the sum of the first `k` (`ColS`, `colR_ok`). From
word 9 on, `pw` reuses the registers of operands' words no later column
reads (`live_facts`).
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
    rw [accW, accW_val32 acc m b N, show 2 * (N + 1) = 2 * N + 1 + 1 by omega_using [], val32_succ, val32_succ,
      dw_split, show acc + 4 * (2 * N) = acc + 8 * N by omega_using [],
      show acc + 4 * (2 * N + 1) = acc + 8 * N + 4 by omega_using [],
      show 32 * (2 * N + 1) = 64 * N + 32 by omega_using [], show 32 * (2 * N) = 64 * N by omega_using [],
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
  | n + 1, h => by rw [colsV, colsV, colsV_congr (fun k hk => h k (by omega_using [hk])), h n (by omega_using [])]

/-! ## The product in registers -/

/-- The registers `mulX` changes: the volatile `r4`, `r5`, `r7`–`r11`, and
`r15`–`r31`, but not `r14`, which Ed448 keeps a public value in. -/
abbrev clobR : List Reg :=
  [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23,
    .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem pw_inj : ∀ j < 15, ∀ k < 15, pw j = pw k → j = k := by decide

theorem pw_facts : ∀ k < 15, pw k ≠ .r4 ∧ pw k ≠ .r5 ∧ pw k ≠ .r6 ∧ pw k ∈ clobR := by decide

theorem op_facts : ∀ i < 7, opA i ≠ .r4 ∧ opA i ≠ .r5 ∧ opB i ≠ .r4 ∧ opB i ≠ .r5 := by decide

/-- An operand's word that a later column reads (`k + 1 ≤ i + 6`) is in none
of column `k`'s accumulator's registers. -/
theorem live_facts' : ∀ k < 13, ∀ i < 7, i + 6 < k + 1 ∨
    ((opA i ≠ pw k ∧ opA i ≠ pw (k + 1) ∧ opA i ≠ pw (k + 2)) ∧
    (opB i ≠ pw k ∧ opB i ≠ pw (k + 1) ∧ opB i ≠ pw (k + 2))) := by decide

theorem live_facts {k : Nat} (hk : k < 13) {i : Nat} (hi : i < 7) (hl : k + 1 ≤ i + 6) :
    (opA i ≠ pw k ∧ opA i ≠ pw (k + 1) ∧ opA i ≠ pw (k + 2)) ∧
    (opB i ≠ pw k ∧ opB i ≠ pw (k + 1) ∧ opB i ≠ pw (k + 2)) :=
  (live_facts' k hk i hi).resolve_left (by omega_using [hl])

theorem pairs_ok : ∀ k < 13, ∀ p ∈ pairs k, p.1 < 7 ∧ p.2 < 7 ∧ k ≤ p.1 + 6 ∧ k ≤ p.2 + 6 := by decide

theorem pairs_cons : ∀ k < 13, pairs k = (pairs k).headD (0, 0) :: (pairs k).tail := by decide

/-- The words of a column's first term are not in its accumulator's two low registers. -/
theorem head_facts : ∀ k < 13, opA ((pairs k).headD (0, 0)).1 ≠ pw k ∧
    opA ((pairs k).headD (0, 0)).1 ≠ pw (k + 1) ∧ opB ((pairs k).headD (0, 0)).2 ≠ pw k ∧
    opB ((pairs k).headD (0, 0)).2 ≠ pw (k + 1) := by decide

/-- The words of a column's later terms are in none of its accumulator's registers. -/
theorem tail_facts : ∀ k < 13, ∀ p ∈ (pairs k).tail, p.1 < 7 ∧ p.2 < 7 ∧
    (opA p.1 ≠ pw k ∧ opA p.1 ≠ pw (k + 1) ∧ opA p.1 ≠ pw (k + 2)) ∧
    (opB p.2 ≠ pw k ∧ opB p.2 ≠ pw (k + 1) ∧ opB p.2 ≠ pw (k + 2)) := by decide

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
    (hp : p.1 < 7 ∧ p.2 < 7 ∧ (opA p.1 ≠ pw k ∧ opA p.1 ≠ pw (k + 1) ∧ opA p.1 ≠ pw (k + 2)) ∧
      (opB p.2 ≠ pw k ∧ opB p.2 ≠ pw (k + 1) ∧ opB p.2 ≠ pw (k + 2))) {s : State}
    (h : TermS (b := b) s0 k s) :
    WP isa (.block (termR k p)) s fun s' => TermS (b := b) s0 k s' ∧
      (v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + opProd s0 p < 2 ^ 192 →
        v3 s' (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + opProd s0 p) := by
  obtain ⟨hi, hj, ⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩ := hp
  obtain ⟨p04, p05, -, p0c⟩ := pw_facts k (by omega_using [hk])
  obtain ⟨p14, p15, -, p1c⟩ := pw_facts (k + 1) (by omega_using [hk])
  obtain ⟨p24, p25, -, p2c⟩ := pw_facts (k + 2) (by omega_using [hk])
  have h01 : pw k ≠ pw (k + 1) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  have h02 : pw k ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  have h12 : pw (k + 1) ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  obtain ⟨a4, a5, -, -⟩ := op_facts p.1 hi
  obtain ⟨-, -, b4, b5⟩ := op_facts p.2 hj
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
    ∀ (ps : List (Nat × Nat)), (∀ p ∈ ps, p.1 < 7 ∧ p.2 < 7 ∧
      (opA p.1 ≠ pw k ∧ opA p.1 ≠ pw (k + 1) ∧ opA p.1 ≠ pw (k + 2)) ∧
      (opB p.2 ≠ pw k ∧ opB p.2 ≠ pw (k + 1) ∧ opB p.2 ≠ pw (k + 2))) →
      ∀ s, TermS (b := b) s0 k s →
      v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + tsum (opProd s0) ps < 2 ^ 192 →
      WP isa (.block (ps.flatMap (termR k))) s fun s' => TermS (b := b) s0 k s' ∧
        v3 s' (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + tsum (opProd s0) ps
  | [], _, s, h, _ => WP.block_nil ⟨h, by simp [tsum]⟩
  | p :: ps, hps, s, h, hb => by
    rw [List.flatMap_cons]
    rw [tsum_cons] at hb
    refine WP.append (termR_ok hk (hps p List.mem_cons_self) h) fun s1 ⟨h1, hv1⟩ => ?_
    have hv1 := hv1 (by omega_using [hb])
    refine WP.mono (termsR_ok hk ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) s1 h1 (by omega_arith))
      fun s2 ⟨h2, hv2⟩ => ⟨h2, ?_⟩
    rw [hv2, hv1, tsum_cons]; omega_using []

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
  omega_arith

/-- Column `k`: its first term, then the others. -/
theorem colR_ok {s0 : State} {k : Nat} (hk : k < 13) {s : State} (h : ColS (b := b) s0 k s) :
    WP isa (.block (colR k)) s (ColS (b := b) s0 (k + 1)) := by
  obtain ⟨p04, p05, -, p0c⟩ := pw_facts k (by omega_using [hk])
  obtain ⟨p14, p15, -, p1c⟩ := pw_facts (k + 1) (by omega_using [hk])
  obtain ⟨p24, p25, -, p2c⟩ := pw_facts (k + 2) (by omega_using [hk])
  have h01 : pw k ≠ pw (k + 1) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  have h02 : pw k ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  have h12 : pw (k + 1) ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  have hcons := pairs_cons k hk
  generalize hp0 : (pairs k).headD (0, 0) = p0 at hcons
  have hmem : p0 ∈ pairs k := by rw [hcons]; exact List.mem_cons_self
  obtain ⟨i0, j0, li0, lj0⟩ := pairs_ok k hk p0 hmem
  obtain ⟨ak, ak1, bk, bk1⟩ := head_facts k hk
  rw [hp0] at ak ak1 bk bk1
  obtain ⟨a4, a5, -, -⟩ := op_facts p0.1 i0
  obtain ⟨-, -, b4, b5⟩ := op_facts p0.2 j0
  have ka : s.gpr (opA p0.1) = s0.gpr (opA p0.1) := (h.ops _ i0 li0).1
  have kb : s.gpr (opB p0.2) = s0.gpr (opB p0.2) := (h.ops _ j0 lj0).2
  unfold colR firstR
  rw [hp0]
  simp only [List.cons_append]
  -- The first term's product, then `pw (k + 2)` cleared, then the sum.
  refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => wp_li (by decide) fun s3 u3 => ?_
  refine acc3_ok h01 h02 h12 p05 fun s4 hv4 hg4 hm4 hrd4 hwr4 hsp4 => ?_
  have hA := (s.gpr (opA p0.1)).isLt
  have hB := (s.gpr (opB p0.2)).isLt
  have e : (s3.gpr .r4).toNat + 2 ^ 64 * (s3.gpr .r5).toNat = opProd s0 p0 := by
    rw [u3.other _ (Ne.symm p24), u3.other _ (Ne.symm p25), u2.other _ (by decide), u1.gpr, u2.gpr,
      u1.other _ a4, u1.other _ b4, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt hA hB)), ka, kb]
    exact Nat.mod_add_div _ _
  have hv3 : v3 s3 (pw k) (pw (k + 1)) (pw (k + 2)) =
      (s.gpr (pw k)).toNat + 2 ^ 64 * (s.gpr (pw (k + 1))).toNat := by
    simp only [v3, u3.gpr, u3.other _ h02, u3.other _ h12, u2.other _ p05, u2.other _ p15,
      u1.other _ p04, u1.other _ p14]
    rfl
  have hl := (s.gpr (pw k)).isLt
  have hh := (s.gpr (pw (k + 1))).isLt
  have hP : opProd s0 p0 < 2 ^ 128 := by
    rw [← e]; have := (s3.gpr .r4).isLt; have := (s3.gpr .r5).isLt; omega_arith
  have hv4' := hv4 (by rw [hv3, Nat.add_assoc, e]; omega_arith)
  rw [hv3, Nat.add_assoc, e] at hv4'
  have hr3 : Rest clobR s s3 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest p2c))
  have hr4 : Rest clobR s3 s4 := ⟨fun r hr' => hg4 r (fun e => hr' (e ▸ p0c)) (fun e => hr' (e ▸ p1c))
    (fun e => hr' (e ▸ p2c)), hrd4, hwr4, hsp4⟩
  have hm4' : s4.mem = s.mem := by rw [hm4, u3.mem, u2.mem, u1.mem]
  -- Through `s4`, a register outside the accumulator and `r4`, `r5` is as it was.
  have keep4 : ∀ r, r ≠ pw k → r ≠ pw (k + 1) → r ≠ pw (k + 2) → r ≠ .r4 → r ≠ .r5 → s4.gpr r = s.gpr r :=
    fun r n0 n1 n2 n4 n5 => by rw [hg4 r n0 n1 n2, u3.other _ n2, u2.other _ n5, u1.other _ n4]
  have hRT : TermS (b := b) s4 k s4 := ⟨h.ctx.of_rest (hr3.trans hr4) (by decide), Rest.refl _ _, rfl,
    fun _ _ _ _ _ _ => rfl⟩
  have htl := tail_facts k hk
  have hF : ∀ p ∈ (pairs k).tail, opProd s4 p = opProd s0 p := fun p hp => by
    obtain ⟨hi, hj, ⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩ := htl p hp
    have hp' : p ∈ pairs k := by rw [hcons]; exact List.mem_cons_of_mem _ hp
    obtain ⟨-, -, li, lj⟩ := pairs_ok k hk p hp'
    obtain ⟨c4, c5, -, -⟩ := op_facts p.1 hi
    obtain ⟨-, -, d4, d5⟩ := op_facts p.2 hj
    simp only [opProd, keep4 _ a0 a1 a2 c4 c5, keep4 _ b0 b1 b2 d4 d5, (h.ops _ hi li).1, (h.ops _ hj lj).2]
  have hts : tsum (opProd s4) (pairs k).tail = tsum (opProd s0) (pairs k).tail := by
    unfold tsum; congr 1; exact List.map_congr_left hF
  have hlt : tsum (opProd s4) (pairs k).tail < 7 * 2 ^ 128 :=
    tsum_lt7 (fun p => Nat.mul_le_mul (by have := (s4.gpr (opA p.1)).isLt; omega_using [])
      (by have := (s4.gpr (opB p.2)).isLt; omega_using [])) (by
        have := pairs_len k hk; rw [hcons] at this; simp only [List.length_cons] at this; omega_using [this])
  refine WP.mono (termsR_ok hk (pairs k).tail (fun p hp => htl p hp) s4 hRT
    (by rw [hv4']; omega_arith)) fun s5 ⟨h5, hv5⟩ => ?_
  rw [hv4', hts] at hv5
  have htot : tsum (opProd s0) (pairs k) = opProd s0 p0 + tsum (opProd s0) (pairs k).tail := by
    rw [hcons, tsum_cons]; rfl
  have hlow : ∀ j < k, s5.gpr (pw j) = s.gpr (pw j) := fun j hj => by
    have n0 : pw j ≠ pw k := fun e => by have := pw_inj _ (by omega_using [hk, hj]) _ (by omega_using [hk]) e; omega_arith
    have n1 : pw j ≠ pw (k + 1) := fun e => by have := pw_inj _ (by omega_using [hk, hj]) _ (by omega_using [hk]) e; omega_arith
    have n2 : pw j ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega_using [hk, hj]) _ (by omega_using [hk]) e; omega_arith
    obtain ⟨j4, j5, -, -⟩ := pw_facts j (by omega_using [hk, hj])
    rw [h5.keep _ n0 n1 n2 j4 j5, keep4 _ n0 n1 n2 j4 j5]
  refine ⟨h5.ctx, h.rest.trans (hr3.trans (hr4.trans h5.rest)), h5.mem.trans (hm4'.trans h.mem),
    fun i hi hl' => ?_, ?_⟩
  · obtain ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩ := live_facts hk hi hl'
    obtain ⟨c4, c5, d4, d5⟩ := op_facts i hi
    exact ⟨by rw [h5.keep _ a0 a1 a2 c4 c5, keep4 _ a0 a1 a2 c4 c5]; exact (h.ops i hi (by omega_using [hl'])).1,
      by rw [h5.keep _ b0 b1 b2 d4 d5, keep4 _ b0 b1 b2 d4 d5]; exact (h.ops i hi (by omega_using [hl'])).2⟩
  · have hv := h.val
    rw [show k + 1 + 1 = k + 2 by omega_using []]
    simp only [pwSum, colsV]
    rw [colsV_congr (fun j hj => by rw [hlow j hj])]
    rw [← pwSum, htot]
    unfold v3 at hv5
    rw [Nat.pow_succ (n := 2 ^ 64)]
    generalize (2 ^ 64) ^ k = K at *
    generalize pwSum s k = S at *
    generalize colsV (fun c => tsum (opProd s0) (pairs c)) k = C at *
    generalize opProd s0 p0 = P0 at *
    generalize tsum (opProd s0) (pairs k).tail = T at *
    generalize (s.gpr (pw k)).toNat = a at *
    generalize (s.gpr (pw (k + 1))).toNat = c at *
    generalize (s5.gpr (pw k)).toNat = a' at *
    generalize (s5.gpr (pw (k + 1))).toNat = c' at *
    generalize (s5.gpr (pw (k + 2))).toNat = d' at *
    generalize 2 ^ 64 = W at *
    rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, hv5,
      show a + W * c + P0 + T = (a + W * c) + (P0 + T) by omega_using [], Nat.mul_add, ← hv]
    omega_using []

/-- The columns, by induction. -/
theorem colsR_ok {s0 : State} : ∀ n ≤ 13, ∀ s, ColS (b := b) s0 0 s →
    WP isa (.block ((List.range n).flatMap colR)) s (ColS (b := b) s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (colsR_ok n (by omega_using [hn]) s h) fun s1 h1 => colR_ok (by omega_using [hn]) h1

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
    calc colsV f n + (2 ^ 64) ^ n * f n < (2 ^ 64) ^ n + (2 ^ 64) ^ n * f n := by omega_arith
      _ = (2 ^ 64) ^ n * (f n + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ (2 ^ 64) ^ n * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega_using [this])

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
      omega_using [hlt, hv, h]
  subst this
  omega_using [hv]

end

end VG.Proof.X448.PPC64LE
