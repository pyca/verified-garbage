module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on PPC64LE: the multiplication in registers

`mulR o x y` stores at `o` a number congruent modulo `p` to `[x] · [y]`
(`mulR_ok`), with its operands in `opA`, `opB` and its product in `pw`:
`productR` loads the operands' words, then adds each column's terms into the
accumulator `pw k, pw (k + 1), pw (k + 2)` (`termR_ok`, by `acc3_ok`), so
that after `k` columns `pw 0, …, pw (k - 1)` and the accumulator hold the sum
of the first `k` (`PInv`, `colR_ok`); `reduceR` is `reduce38` with the
product's words read from `pw` (`lowsR_ok`, `highsR_ok`, `reduceR_ok`).
-/

-- separate module: the multiplication's proof, like `Mul`'s; the slots' lemmas change without rebuilding it.

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P)

/-- The registers `mulR` changes. -/
abbrev clobR : List Reg :=
  [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23,
    .r24, .r25, .r26, .r27, .r28, .r29, .r30]

theorem clob_sub : ∀ r ∈ clob, r ∈ clobR := by decide

theorem pw_inj : ∀ j < 9, ∀ k < 9, pw j = pw k → j = k := by decide

theorem pw_facts : ∀ k < 9, pw k ≠ .r4 ∧ pw k ≠ .r5 ∧ pw k ≠ .r6 ∧ pw k ≠ .r7 ∧ pw k ∈ clobR ∧
    (∀ i < 4, pw k ≠ opA i ∧ pw k ≠ opB i) ∧ (∀ i < 4, pw k ≠ wreg i) := by decide

theorem op_facts : ∀ i < 4, opA i ≠ .r4 ∧ opA i ≠ .r6 ∧ opA i ≠ .r7 ∧ opB i ≠ .r4 ∧ opB i ≠ .r6 ∧
    opB i ≠ .r7 ∧ opA i ∈ clobR ∧ opB i ∈ clobR ∧ (∀ j < 4, opA i ≠ opB j) ∧
    (∀ j < 4, opA i = opA j → i = j) ∧ (∀ j < 4, opB i = opB j → i = j) := by decide

section
variable {b : Addr}

/-! ## The operands -/

/-- After `loadOps x y`: the operands' words in `opA` and `opB`. -/
theorem loadOps_ok {x y : Nat} (hx : x + 32 ≤ 4096) (hy : y + 32 ≤ 4096) (hx4 : x % 4 = 0)
    (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx b s' → Rest clobR s s' → s'.mem = s.mem →
      (∀ i < 4, (s'.gpr (opA i)).toNat = ew s.mem b x i) →
      (∀ j < 4, (s'.gpr (opB j)).toNat = ew s.mem b y j) → WP isa (.block is) s' Q) :
    WP isa (.block (loadOps x y ++ is)) s Q := by
  have ld : ∀ (t : State) (r : Reg) (d : Nat), Ctx b t → r ∈ clobR → d + 8 ≤ 4096 → d % 4 = 0 →
      ∀ (is' : List Instr) (Q' : State → Prop),
      (∀ t', Ctx b t' → Rest clobR t t' → t'.mem = t.mem → t'.gpr r = t.mem.readW (b + BitVec.ofNat 64 d) 64 →
        (∀ r', r' ≠ r → t'.gpr r' = t.gpr r') → WP isa (.block is') t' Q') →
      WP isa (.block (.load .d r .r6 d :: is')) t Q' := by
    intro t r d hct hr hd hd4 is' Q' kk
    refine ld0_ok hct hd hd4 fun t' u => kk t' (hct.of_rest (u.rest hr) (by decide)) (u.rest hr) u.mem u.gpr u.other
  simp only [loadOps, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, opA, opB, Nat.reduceEqDiff, ↓reduceIte]
  refine ld s .r14 _ hc (by decide) (by omega_using [hx]) (by omega_using [hx4]) _ _ fun s1 c1 r1 m1 g1 o1 => ?_
  refine ld s1 .r15 _ c1 (by decide) (by omega_using [hx]) (by omega_using [hx4]) _ _ fun s2 c2 r2 m2 g2 o2 => ?_
  refine ld s2 .r16 _ c2 (by decide) (by omega_using [hx]) (by omega_using [hx4]) _ _ fun s3 c3 r3 m3 g3 o3 => ?_
  refine ld s3 .r17 _ c3 (by decide) (by omega_using [hx]) (by omega_using [hx4]) _ _ fun s4 c4 r4 m4 g4 o4 => ?_
  refine ld s4 .r18 _ c4 (by decide) (by omega_using [hy]) (by omega_using [hy4]) _ _ fun s5 c5 r5 m5 g5 o5 => ?_
  refine ld s5 .r19 _ c5 (by decide) (by omega_using [hy]) (by omega_using [hy4]) _ _ fun s6 c6 r6 m6 g6 o6 => ?_
  refine ld s6 .r20 _ c6 (by decide) (by omega_using [hy]) (by omega_using [hy4]) _ _ fun s7 c7 r7 m7 g7 o7 => ?_
  refine ld s7 .r21 _ c7 (by decide) (by omega_using [hy]) (by omega_using [hy4]) _ _ fun s8 c8 r8 m8 g8 o8 => ?_
  have hm : ∀ t : State, t.mem = s.mem → t.mem = s.mem := fun _ h => h
  have e2 : s1.mem = s.mem := m1
  have e3 : s2.mem = s.mem := m2.trans m1
  have e4 : s3.mem = s.mem := m3.trans e3
  have e5 : s4.mem = s.mem := m4.trans e4
  have e6 : s5.mem = s.mem := m5.trans e5
  have e7 : s6.mem = s.mem := m6.trans e6
  have e8 : s7.mem = s.mem := m7.trans e7
  refine k s8 c8 (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans r8)))))))
    (m8.trans e8) (fun i hi => ?_) (fun j hj => ?_)
  · have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
    rcases this with rfl | rfl | rfl | rfl <;> simp only [opA, Nat.reduceEqDiff, ↓reduceIte]
    · rw [o8 _ (by decide), o7 _ (by decide), o6 _ (by decide), o5 _ (by decide), o4 _ (by decide),
        o3 _ (by decide), o2 _ (by decide), g1]; rfl
    · rw [o8 _ (by decide), o7 _ (by decide), o6 _ (by decide), o5 _ (by decide), o4 _ (by decide),
        o3 _ (by decide), g2, e2]; rfl
    · rw [o8 _ (by decide), o7 _ (by decide), o6 _ (by decide), o5 _ (by decide), o4 _ (by decide),
        g3, e3]; rfl
    · rw [o8 _ (by decide), o7 _ (by decide), o6 _ (by decide), o5 _ (by decide), g4, e4]; rfl
  · have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega_using [hj]
    rcases this with rfl | rfl | rfl | rfl <;> simp only [opB, Nat.reduceEqDiff, ↓reduceIte]
    · rw [o8 _ (by decide), o7 _ (by decide), o6 _ (by decide), g5, e5]; rfl
    · rw [o8 _ (by decide), o7 _ (by decide), g6, e6]; rfl
    · rw [o8 _ (by decide), g7, e7]; rfl
    · rw [g8, e8]; rfl

/-! ## The columns -/

/-- From `s0`, the registers a column's terms keep. -/
structure RT (s0 : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clobR s0 s
  mem : s.mem = s0.mem
  keep : ∀ r, r ≠ pw k → r ≠ pw (k + 1) → r ≠ pw (k + 2) → r ≠ .r4 → r ≠ .r7 → s.gpr r = s0.gpr r

/-- The product of the operands' words `i` and `j`. -/
def opF (s : State) (p : Nat × Nat) : Nat := (s.gpr (opA p.1)).toNat * (s.gpr (opB p.2)).toNat

/-- A term `a_i b_j` of column `k`. -/
theorem termR_ok {s0 : State} {k i j : Nat} (hk : k < 7) (hi : i < 4) (hj : j < 4) {s : State}
    (h : RT (b := b) s0 k s) :
    WP isa (.block (termR k (i, j))) s fun s' => RT (b := b) s0 k s' ∧
      (v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + opF s0 (i, j) < 2 ^ 192 →
        v3 s' (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + opF s0 (i, j)) := by
  obtain ⟨p04, -, -, p07, p0c, p0o, -⟩ := pw_facts k (by omega_using [hk])
  obtain ⟨p14, -, -, p17, p1c, p1o, -⟩ := pw_facts (k + 1) (by omega_using [hk])
  obtain ⟨p24, -, -, p27, p2c, p2o, -⟩ := pw_facts (k + 2) (by omega_using [hk])
  have h01 : pw k ≠ pw (k + 1) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  have h02 : pw k ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  have h12 : pw (k + 1) ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  obtain ⟨a4, -, a7, -, -, -, -, -, -, -, -⟩ := op_facts i hi
  obtain ⟨-, -, -, b4, -, b7, -, -, -, -, -⟩ := op_facts j hj
  have ka : s.gpr (opA i) = s0.gpr (opA i) :=
    h.keep _ (fun e => (p0o i hi).1 e.symm) (fun e => (p1o i hi).1 e.symm) (fun e => (p2o i hi).1 e.symm) a4 a7
  have kb : s.gpr (opB j) = s0.gpr (opB j) :=
    h.keep _ (fun e => (p0o j hj).2 e.symm) (fun e => (p1o j hj).2 e.symm) (fun e => (p2o j hj).2 e.symm) b4 b7
  simp only [termR]
  refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => ?_
  refine acc3_ok h01 h02 h12 p04 fun s3 hv3 hg3 hm3 hrd3 hwr3 hsp3 => WP.block_nil ?_
  have hA := (s.gpr (opA i)).isLt
  have hB := (s.gpr (opB j)).isLt
  have g1a : s1.gpr (opA i) = s.gpr (opA i) := u1.other _ a7
  have g1b : s1.gpr (opB j) = s.gpr (opB j) := u1.other _ b7
  have elo : (s2.gpr .r7).toNat = opF s0 (i, j) % 2 ^ 64 := by
    rw [u2.other _ (by decide), u1.gpr, BitVec.toNat_mul, ka, kb]; rfl
  have ehi : (s2.gpr .r4).toNat = opF s0 (i, j) / 2 ^ 64 := by
    rw [u2.gpr, g1a, g1b, ka, kb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    · rfl
    · rw [← ka, ← kb]; exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt hA hB)
  have e : (s2.gpr .r7).toNat + 2 ^ 64 * (s2.gpr .r4).toNat = opF s0 (i, j) := by
    rw [elo, ehi]; exact Nat.mod_add_div _ _
  have hv2 : v3 s2 (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) := by
    simp only [v3, u2.other _ p04, u2.other _ p14, u2.other _ p24, u1.other _ p07, u1.other _ p17,
      u1.other _ p27]
  have hr2 : Rest clobR s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hr3 : Rest clobR s2 s3 := ⟨fun r hr' => hg3 r (fun e => hr' (e ▸ p0c)) (fun e => hr' (e ▸ p1c))
    (fun e => hr' (e ▸ p2c)), hrd3, hwr3, hsp3⟩
  have hm : s3.mem = s.mem := by rw [hm3, u2.mem, u1.mem]
  refine ⟨⟨h.ctx.of_rest (hr2.trans hr3) (by decide), h.rest.trans (hr2.trans hr3), hm.trans h.mem,
    fun r n0 n1 n2 n4 n7 => ?_⟩, fun hb => ?_⟩
  · rw [hg3 r n0 n1 n2, u2.other _ n4, u1.other _ n7]; exact h.keep r n0 n1 n2 n4 n7
  · rw [hv3 (by rw [hv2, Nat.add_assoc, e]; exact hb), hv2, Nat.add_assoc, e]

/-- A column's terms, by induction on them. -/
theorem termsR_ok {s0 : State} {k : Nat} (hk : k < 7) :
    ∀ (ps : List (Nat × Nat)), (∀ p ∈ ps, p.1 < 4 ∧ p.2 < 4) → ∀ s, RT (b := b) s0 k s →
      v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + tsum (opF s0) ps < 2 ^ 192 →
      WP isa (.block (ps.flatMap (termR k))) s fun s' => RT (b := b) s0 k s' ∧
        v3 s' (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + tsum (opF s0) ps
  | [], _, s, h, _ => WP.block_nil ⟨h, by simp [tsum]⟩
  | (i, j) :: ps, hps, s, h, hb => by
    rw [List.flatMap_cons]
    rw [tsum_cons] at hb
    obtain ⟨hp1, hp2⟩ := hps (i, j) (List.mem_cons_self ..)
    refine WP.append (termR_ok (i := i) (j := j) hk hp1 hp2 h) fun s1 ⟨h1, hv1⟩ => ?_
    have hv1 := hv1 (by omega_using [hb])
    refine WP.mono (termsR_ok hk ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) s1 h1 (by omega_arith))
      fun s2 ⟨h2, hv2⟩ => ⟨h2, ?_⟩
    rw [hv2, hv1, tsum_cons]; omega_using []

/-- The value of the words `pw 0`, …, `pw (k - 1)`. -/
abbrev pwV (s : State) (k : Nat) : Nat := colsV (fun j => (s.gpr (pw j)).toNat) k

/-- After `k` columns, from `s0`: the operands' words as they were, and
`pw 0`, …, `pw (k - 1)` and the accumulator `pw k, pw (k + 1)` the sum of
the first `k` columns. -/
structure PInv (s0 : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clobR s0 s
  mem : s.mem = s0.mem
  ops : ∀ i < 4, s.gpr (opA i) = s0.gpr (opA i) ∧ s.gpr (opB i) = s0.gpr (opB i)
  val : pwV s k + (2 ^ 64) ^ k * ((s.gpr (pw k)).toNat + 2 ^ 64 * (s.gpr (pw (k + 1))).toNat) =
    colsV (fun c => tsum (opF s0) (colPairs c)) k

theorem colsV_congr' {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = g k) → colsV f n = colsV g n
  | 0, _ => rfl
  | n + 1, h => by rw [colsV, colsV, colsV_congr' (fun k hk => h k (by omega_using [hk])), h n (by omega_using [])]

/-- Column `k`. -/
theorem colR_ok {s0 : State} {k : Nat} (hk : k < 7) {s : State} (h : PInv (b := b) s0 k s) :
    WP isa (.block (colR k)) s (PInv (b := b) s0 (k + 1)) := by
  obtain ⟨-, -, -, -, p2c, p2o, -⟩ := pw_facts (k + 2) (by omega_using [hk])
  unfold colR
  refine wp_li (by decide) fun s1 u1 => ?_
  have hr1 : Rest clobR s s1 := u1.rest p2c
  have hRT : RT (b := b) s1 k s1 := ⟨h.ctx.of_rest hr1 (by decide), Rest.refl _ _, rfl, fun _ _ _ _ _ _ => rfl⟩
  have hops : ∀ i < 4, s1.gpr (opA i) = s0.gpr (opA i) ∧ s1.gpr (opB i) = s0.gpr (opB i) := fun i hi =>
    ⟨by rw [u1.other _ (fun e => (p2o i hi).1 e.symm)]; exact (h.ops i hi).1,
      by rw [u1.other _ (fun e => (p2o i hi).2 e.symm)]; exact (h.ops i hi).2⟩
  have hF : ∀ p ∈ colPairs k, opF s1 p = opF s0 p := fun p hp => by
    obtain ⟨h1, h2⟩ := colPairs_ok k (by omega_using [hk]) p hp
    simp only [opF, (hops _ h1).1, (hops _ h2).2]
  have hts : tsum (opF s1) (colPairs k) = tsum (opF s0) (colPairs k) := by
    unfold tsum; congr 1; exact List.map_congr_left hF
  have hlt : tsum (opF s1) (colPairs k) < 4 * 2 ^ 128 :=
    tsum_lt (fun p => Nat.mul_le_mul (by have := (s1.gpr (opA p.1)).isLt; omega_using [])
      (by have := (s1.gpr (opB p.2)).isLt; omega_using [])) (colPairs_len k (by omega_using [hk]))
  have g2 : s1.gpr (pw (k + 2)) = 0 := u1.gpr
  have h01 : pw k ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  have h11 : pw (k + 1) ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega_using [hk]) _ (by omega_using [hk]) e; omega_using [this]
  have hv0 : v3 s1 (pw k) (pw (k + 1)) (pw (k + 2)) =
      (s.gpr (pw k)).toNat + 2 ^ 64 * (s.gpr (pw (k + 1))).toNat := by
    simp only [v3, g2, u1.other _ h01, u1.other _ h11]; rfl
  have hl := (s.gpr (pw k)).isLt
  have hh := (s.gpr (pw (k + 1))).isLt
  refine WP.mono (termsR_ok hk (colPairs k) (fun p hp => colPairs_ok k (by omega_using [hk]) p hp) s1 hRT
    (by rw [hv0]; omega_arith)) fun s2 ⟨h2, hv2⟩ => ?_
  have hlow : ∀ j < k, s2.gpr (pw j) = s.gpr (pw j) := fun j hj => by
    have n0 : pw j ≠ pw k := fun e => by have := pw_inj _ (by omega_using [hk, hj]) _ (by omega_using [hk]) e; omega_using [hj, this]
    have n1 : pw j ≠ pw (k + 1) := fun e => by have := pw_inj _ (by omega_using [hk, hj]) _ (by omega_using [hk]) e; omega_using [hj, this]
    have n2 : pw j ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega_using [hk, hj]) _ (by omega_using [hk]) e; omega_using [hj, this]
    obtain ⟨j4, -, -, j7, -⟩ := pw_facts j (by omega_using [hk, hj])
    rw [h2.keep _ n0 n1 n2 j4 j7, u1.other _ n2]
  refine ⟨h2.ctx, h.rest.trans (hr1.trans h2.rest), h2.mem.trans (by rw [u1.mem, h.mem]), fun i hi => ?_, ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -⟩ := op_facts i hi
    have k0 := pw_facts k (by omega_using [hk]); have k1 := pw_facts (k + 1) (by omega_using [hk])
    have k2 := pw_facts (k + 2) (by omega_using [hk]); have oi := op_facts i hi
    refine ⟨?_, ?_⟩
    · rw [h2.keep _ (fun e => (k0.2.2.2.2.2.1 i hi).1 e.symm) (fun e => (k1.2.2.2.2.2.1 i hi).1 e.symm)
        (fun e => (k2.2.2.2.2.2.1 i hi).1 e.symm) oi.1 oi.2.2.1]
      exact (hops i hi).1
    · rw [h2.keep _ (fun e => (k0.2.2.2.2.2.1 i hi).2 e.symm) (fun e => (k1.2.2.2.2.2.1 i hi).2 e.symm)
        (fun e => (k2.2.2.2.2.2.1 i hi).2 e.symm) oi.2.2.2.1 oi.2.2.2.2.2.1]
      exact (hops i hi).2
  · have hv := h.val
    rw [show k + 1 + 1 = k + 2 by omega_using []]
    simp only [pwV, colsV]
    rw [colsV_congr' (fun j hj => by rw [hlow j hj])]
    rw [← pwV, ← hts]
    rw [hv0] at hv2
    unfold v3 at hv2
    rw [Nat.pow_succ (n := 2 ^ 64)]
    generalize (2 ^ 64) ^ k = K at *
    generalize pwV s k = S at *
    generalize colsV (fun c => tsum (opF s0) (colPairs c)) k = C at *
    generalize tsum (opF s1) (colPairs k) = T at *
    generalize (s.gpr (pw k)).toNat = a at *
    generalize (s.gpr (pw (k + 1))).toNat = c at *
    generalize (s2.gpr (pw k)).toNat = a' at *
    generalize (s2.gpr (pw (k + 1))).toNat = c' at *
    generalize (s2.gpr (pw (k + 2))).toNat = d' at *
    generalize 2 ^ 64 = W at *
    rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, hv2, ← hv, Nat.mul_add K (a + W * c) T]
    omega_using []

/-- The columns, by induction. -/
theorem colsR_ok {s0 : State} : ∀ n ≤ 7, ∀ s, PInv (b := b) s0 0 s →
    WP isa (.block ((List.range n).flatMap colR)) s (PInv (b := b) s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (colsR_ok n (by omega_using [hn]) s h) fun s1 h1 => colR_ok (by omega_using [hn]) h1

/-- The columns sum to the product of the operands' words. -/
theorem colsR_sum (s0 : State) :
    colsV (fun c => tsum (opF s0) (colPairs c)) 7 =
      val4 (fun i => (s0.gpr (opA i)).toNat) * val4 (fun j => (s0.gpr (opB j)).toNat) := by
  rw [← mulCols_sum]
  show _ = colsV _ 7 + (2 ^ 64) ^ 7 * mulCs _ _ 7
  rw [mulCs, show colPairs 7 = [] by decide, tsum, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero]
  rfl

/-- `productR x y`: the words of `[x] · [y]` in `pw 0`, …, `pw 7`. -/
theorem productR_ok {x y : Nat} (hx : x + 32 ≤ 4096) (hy : y + 32 ≤ 4096) (hx4 : x % 4 = 0)
    (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (productR x y)) s fun s' => Ctx b s' ∧ Rest clobR s s' ∧ s'.mem = s.mem ∧
      pwV s' 8 = V s.mem b x * V s.mem b y := by
  unfold productR
  simp only [List.append_assoc]
  refine loadOps_ok hx hy hx4 hy4 hc fun s1 c1 r1 m1 ea eb => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s2 u2 => wp_li (by decide) fun s3 u3 => ?_
  have hr3 : Rest clobR s1 s3 := (u2.rest (by decide)).trans (u3.rest (by decide))
  have hinit : PInv (b := b) s3 0 s3 := ⟨c1.of_rest hr3 (by decide), Rest.refl _ _, rfl,
    fun _ _ => ⟨rfl, rfl⟩, by
      have e1 : s3.gpr .r23 = 0 := u3.gpr
      have e0 : s3.gpr .r22 = 0 := by rw [u3.other .r22 (by decide)]; exact u2.gpr
      simp only [pwV, colsV, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
        show pw (0 + 1) = .r23 from rfl, show pw 0 = .r22 from rfl]
      rw [e0, e1]; rfl⟩
  refine WP.mono (colsR_ok 7 (Nat.le_refl _) s3 hinit) fun s4 h4 => ⟨h4.ctx, r1.trans (hr3.trans h4.rest),
    by rw [h4.mem, u3.mem, u2.mem, m1], ?_⟩
  have hv := h4.val
  have ho3 : ∀ i < 4, s3.gpr (opA i) = s1.gpr (opA i) ∧ s3.gpr (opB i) = s1.gpr (opB i) := fun i hi => by
    have oi := op_facts i hi
    have p0 := pw_facts 0 (by decide); have p1 := pw_facts 1 (by decide)
    exact ⟨by rw [u3.other _ (fun e => (p1.2.2.2.2.2.1 i hi).1 e.symm),
        u2.other _ (fun e => (p0.2.2.2.2.2.1 i hi).1 e.symm)],
      by rw [u3.other _ (fun e => (p1.2.2.2.2.2.1 i hi).2 e.symm),
        u2.other _ (fun e => (p0.2.2.2.2.2.1 i hi).2 e.symm)]⟩
  have hX : val4 (fun i => (s3.gpr (opA i)).toNat) = V s.mem b x := by
    rw [V_eq4]; exact val4_congr fun i hi => by rw [(ho3 i hi).1, ea i hi]
  have hY : val4 (fun j => (s3.gpr (opB j)).toNat) = V s.mem b y := by
    rw [V_eq4]; exact val4_congr fun j hj => by rw [(ho3 j hj).2, eb j hj]
  rw [colsR_sum, hX, hY] at hv
  have hlt : V s.mem b x * V s.mem b y < (2 ^ 64) ^ 8 := by
    have := V_lt s.mem b x; have := V_lt s.mem b y
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (by assumption) (by assumption)) (by decide)
  have h8 := (s4.gpr (pw 8)).isLt
  have hp7 : pwV s4 7 < (2 ^ 64) ^ 7 := by
    have : ∀ n, pwV s4 n < (2 ^ 64) ^ n := by
      intro n; induction n with
      | zero => simp [pwV, colsV]
      | succ n ih =>
        simp only [pwV, colsV] at ih ⊢
        have := (s4.gpr (pw n)).isLt
        rw [Nat.pow_succ]
        calc colsV (fun j => (s4.gpr (pw j)).toNat) n + (2 ^ 64) ^ n * (s4.gpr (pw n)).toNat
            < (2 ^ 64) ^ n + (2 ^ 64) ^ n * (s4.gpr (pw n)).toNat := by omega_using [ih]
          _ = (2 ^ 64) ^ n * ((s4.gpr (pw n)).toNat + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
          _ ≤ (2 ^ 64) ^ n * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega_using [])
    exact this 7
  simp only [pwV, colsV] at hv hp7 ⊢
  generalize colsV (fun j => (s4.gpr (pw j)).toNat) 7 = S at *
  generalize (s4.gpr (pw 7)).toNat = a at *
  generalize (s4.gpr (pw (7 + 1))).toNat = c at *
  generalize V s.mem b x * V s.mem b y = XY at *
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · simpa using hv
  · exfalso
    have : (2 ^ 64) ^ 7 * (2 ^ 64 * c) ≥ (2 ^ 64) ^ 8 := by
      rw [← Nat.mul_assoc, ← Nat.pow_succ]; exact Nat.le_mul_of_pos_right _ hc0
    omega_using [hlt, hv, hc0]

/-! ## The reduction -/

theorem opR_ok {d n src : Reg} (hn4 : n ≠ .r4) {s : State} (h5 : s.gpr .r5 = 38) (hi e : Bool) :
    WP isa (.block (opR d n src hi e)) s fun s' =>
      (s'.gpr d).toNat + 2 ^ 64 * s'.ca.toNat =
        (s.gpr n).toNat + part hi (s.gpr src).toNat + (if e then s.ca.toNat else 0) ∧
      s'.ca.toNat ≤ 1 ∧ Rest [.r4, d] s s' ∧ s'.mem = s.mem := by
  have t38 : (38 : BitVec 64).toNat = 38 := rfl
  have hX := (s.gpr src).isLt
  have ex1 : exec (if hi then Instr.mulhu .r4 src .r5 else .mul .r4 src .r5) s =
      some (s.write .r4 (if hi then BitVec.ofNat 64 ((s.gpr src).toNat * (s.gpr .r5).toNat / 2 ^ 64)
        else s.gpr src * s.gpr .r5)) := by
    cases hi <;> rfl
  refine WP.cons ex1 ?_
  generalize hs1 : s.write .r4 _ = s1
  have g4 : (s1.gpr .r4).toNat = part hi (s.gpr src).toNat := by
    rw [← hs1, RegUpd.gpr_write_self]
    cases hi
    · simp only [Bool.false_eq_true, ↓reduceIte, part]; rw [BitVec.toNat_mul, h5, t38]
    · simp only [↓reduceIte, part]; rw [h5, t38, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
  have gn : s1.gpr n = s.gpr n := by rw [← hs1, RegUpd.gpr_write_of_ne _ _ hn4]
  have c1 : s1.ca = s.ca := by rw [← hs1, RegUpd.ca_write]
  have m1 : s1.mem = s.mem := by rw [← hs1, RegUpd.mem_write]
  have r1 : Rest [.r4, d] s s1 := by rw [← hs1]; exact (Upd.write _ _ _).rest (by simp)
  cases e
  · refine wp_addc fun s2 u2 => WP.block_nil ⟨?_, u2.ca, r1.trans (u2.rest (by simp)), by rw [u2.mem, m1]⟩
    rw [u2.val, gn, g4]; simp
  · refine wp_adde fun s2 u2 => WP.block_nil ⟨?_, u2.ca, r1.trans (u2.rest (by simp)), by rw [u2.mem, m1]⟩
    rw [u2.val, gn, g4, c1]; simp

/-- The low words: `rv4 + 2²⁵⁶ CA = L + lo(38 H)`, `L`, `H` the halves of the product in `pw`. -/
theorem lowsR_ok {s : State} (h5 : s.gpr .r5 = 38) :
    WP isa (.block ((List.range 4).flatMap redLoR)) s fun s' =>
      rv4 s' + 2 ^ 256 * s'.ca.toNat =
        val4 (fun k => (s.gpr (pw k)).toNat) + val4 (fun k => part false (s.gpr (pw (4 + k))).toNat) ∧
      Rest [.r4, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_singleton, List.append_assoc, redLoR]
  refine WP.append (opR_ok (d := wreg 0) (n := pw 0) (src := pw (4 + 0)) (by decide) h5 false (0 != 0)) fun s1 ⟨v1, c1, r1, m1⟩ => ?_
  refine WP.append (opR_ok (d := wreg 1) (n := pw 1) (src := pw (4 + 1)) (by decide) (by rw [r1.gpr _ (by decide), h5]) false (1 != 0)) fun s2 ⟨v2, c2, r2, m2⟩ => ?_
  refine WP.append (opR_ok (d := wreg 2) (n := pw 2) (src := pw (4 + 2)) (by decide) (by rw [r2.gpr _ (by decide), r1.gpr _ (by decide), h5]) false (2 != 0))
    fun s3 ⟨v3', c3, r3, m3⟩ => ?_
  refine WP.mono (opR_ok (d := wreg 3) (n := pw 3) (src := pw (4 + 3)) (by decide) (by rw [r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide), h5])
    false (3 != 0)) fun s4 ⟨v4, c4, r4, m4⟩ => ⟨?_, ?_, by rw [m4, m3, m2, m1]⟩
  · have q1 : ∀ r ∈ [pw 1, pw 2, pw 3, pw 5, pw 6, pw 7], s1.gpr r = s.gpr r := by
      intro r hr; exact r1.gpr _ (by revert hr; revert r; decide)
    have q2 : ∀ r ∈ [pw 2, pw 3, pw 6, pw 7], s2.gpr r = s1.gpr r := by
      intro r hr; exact r2.gpr _ (by revert hr; revert r; decide)
    have q3 : ∀ r ∈ [pw 3, pw 7], s3.gpr r = s2.gpr r := by
      intro r hr; exact r3.gpr _ (by revert hr; revert r; decide)
    simp only [show (0 != 0) = false from rfl, show (1 != 0) = true from rfl,
      show (2 != 0) = true from rfl, show (3 != 0) = true from rfl, Bool.false_eq_true,
      ↓reduceIte, Nat.reduceAdd] at v1 v2 v3' v4
    rw [q1 _ (by simp), q1 _ (by simp)] at v2
    rw [q2 _ (by simp), q2 _ (by simp), q1 _ (by simp), q1 _ (by simp)] at v3'
    rw [q3 _ (by simp), q3 _ (by simp), q2 _ (by simp), q2 _ (by simp), q1 _ (by simp), q1 _ (by simp)] at v4
    have e8 : s4.gpr (wreg 0) = s1.gpr (wreg 0) := by
      rw [r4.gpr _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide)]
    have e9 : s4.gpr (wreg 1) = s2.gpr (wreg 1) := by
      rw [r4.gpr _ (by decide), r3.gpr _ (by decide)]
    have e10 : s4.gpr (wreg 2) = s3.gpr (wreg 2) := by rw [r4.gpr _ (by decide)]
    simp only [rv4, val4, e8, e9, e10, Nat.reduceAdd]
    omega_arith
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      (r4.mono (by decide))))

/-- The high words of `38 H`, one word up: into `r9`–`r11` and the top word `r7`. -/
theorem highsR_ok {s : State} (h5 : s.gpr .r5 = 38) (h7 : (s.gpr .r7).toNat ≤ 1) :
    WP isa (.block ((List.range 4).flatMap redHiR)) s fun s' =>
      rv4 s' + 2 ^ 256 * (s'.gpr .r7).toNat = rv4 s + 2 ^ 256 * (s.gpr .r7).toNat +
        2 ^ 64 * val4 (fun k => part true (s.gpr (pw (4 + k))).toNat) ∧
      (s'.gpr .r7).toNat ≤ 39 ∧ Rest [.r4, .r7, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_singleton, List.append_assoc, redHiR]
  simp only [show (0 != 0) = false from rfl, show (1 != 0) = true from rfl,
      show (2 != 0) = true from rfl, show (3 != 0) = true from rfl, Nat.reduceEqDiff, ↓reduceIte,
      Nat.reduceAdd, wreg]
  refine WP.append (opR_ok (d := .r9) (n := .r9) (src := pw 4) (by decide) h5 true false) fun s1 ⟨v1, c1, r1, m1⟩ => ?_
  refine WP.append (opR_ok (d := .r10) (n := .r10) (src := pw 5) (by decide) (by rw [r1.gpr _ (by decide), h5]) true true) fun s2 ⟨v2, c2, r2, m2⟩ => ?_
  refine WP.append (opR_ok (d := .r11) (n := .r11) (src := pw 6) (by decide) (by rw [r2.gpr _ (by decide), r1.gpr _ (by decide), h5]) true true)
    fun s3 ⟨v3', c3, r3, m3⟩ => ?_
  refine WP.mono (opR_ok (d := .r7) (n := .r7) (src := pw 7) (by decide) (by rw [r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide), h5])
    true true) fun s4 ⟨v4, c4, r4, m4⟩ => ?_
  simp only [Bool.false_eq_true, ↓reduceIte] at v1 v2 v3' v4
  have g5 : s1.gpr (pw 5) = s.gpr (pw 5) := r1.gpr _ (by decide)
  have g6 : s2.gpr (pw 6) = s.gpr (pw 6) := by rw [r2.gpr _ (by decide), r1.gpr _ (by decide)]
  have g7 : s3.gpr (pw 7) = s.gpr (pw 7) := by
    rw [r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide)]
  rw [g5] at v2; rw [g6] at v3'; rw [g7] at v4
  have p0 := part_hi_lt _ (s.gpr (pw 4)).isLt
  have p1 := part_hi_lt _ (s.gpr (pw 5)).isLt
  have p2 := part_hi_lt _ (s.gpr (pw 6)).isLt
  have p3 := part_hi_lt _ (s.gpr (pw 7)).isLt
  have e7 : s3.gpr .r7 = s.gpr .r7 := by
    rw [r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide)]
  rw [e7] at v4
  have hl7 := (s4.gpr .r7).isLt
  refine ⟨?_, by omega_using [h7, c3, v4, p3], (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      (r4.mono (by decide)))), by rw [m4, m3, m2, m1]⟩
  have e8 : s4.gpr .r8 = s.gpr .r8 := by
    rw [r4.gpr _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide)]
  have e9 : s4.gpr .r9 = s1.gpr .r9 := by
    rw [r4.gpr _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide)]
  have e10 : s4.gpr .r10 = s2.gpr .r10 := by rw [r4.gpr _ (by decide), r3.gpr _ (by decide)]
  have e11 : s4.gpr .r11 = s3.gpr .r11 := by rw [r4.gpr _ (by decide)]
  have f10 : s1.gpr .r10 = s.gpr .r10 := r1.gpr _ (by decide)
  have f11 : s2.gpr .r11 = s.gpr .r11 := by rw [r2.gpr _ (by decide), r1.gpr _ (by decide)]
  rw [f10] at v2; rw [f11] at v3'
  simp only [rv4, val4, wreg, Nat.reduceEqDiff, ↓reduceIte, e8, e9, e10, e11, Nat.reduceAdd]
  omega_arith

/-- The eight words in `pw` are their halves. -/
theorem pwV_halves (s : State) :
    pwV s 8 = val4 (fun k => (s.gpr (pw k)).toNat) + 2 ^ 256 * val4 (fun k => (s.gpr (pw (4 + k))).toNat) := by
  simp only [pwV, colsV, val4, Nat.reduceAdd]
  omega_arith

/-- `reduceR o`: a number congruent to the product in `pw`, at `o`. -/
theorem reduceR_ok {o : Nat} (ho : o + 32 ≤ 4096) (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (reduceR o)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      V s'.mem b o % P = pwV s 8 % P := by
  unfold reduceR
  simp only [List.cons_append, List.append_assoc]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  have hp1 : ∀ k < 8, s1.gpr (pw k) = s.gpr (pw k) := fun k hk =>
    u1.other _ (pw_facts k (by omega_using [hk])).2.1
  refine WP.append (lowsR_ok (by rw [u1.gpr]; rfl)) fun s2 ⟨v2, r2, m2⟩ => ?_
  have hc2 := hc1.of_rest r2 (by decide)
  refine WP.cons (exec_li (by decide)) (wp_addze fun s3 u3 => ?_)
  have v3 := u3.val
  rw [RegUpd.gpr_write_self, RegUpd.ca_write] at v3
  have z : (BitVec.ofNat 64 0).toNat = 0 := rfl
  rw [z] at v3
  have c2 : s2.ca.toNat ≤ 1 := Bool.toNat_le _
  have l3 := (s3.gpr .r7).isLt
  have e3 : (s3.gpr .r7).toNat = s2.ca.toNat := by omega_using [v3, c2]
  have rv3 : rv4 s3 = rv4 s2 := by
    simp only [rv4, val4, wreg, Nat.reduceEqDiff, ↓reduceIte]
    rw [u3.other _ (by decide), u3.other _ (by decide), u3.other _ (by decide), u3.other _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide)]
  have r3 : Rest [.r4, .r7, .r8, .r9, .r10, .r11] s2 s3 :=
    ((Upd.write _ _ _).rest (by decide)).trans (u3.rest (by decide))
  have m3 : s3.mem = s2.mem := by rw [u3.mem, RegUpd.mem_write]
  have h53 : s3.gpr .r5 = 38 := by
    rw [r3.gpr _ (by decide), r2.gpr _ (by decide), u1.gpr]; rfl
  have hp3 : ∀ k < 8, s3.gpr (pw k) = s.gpr (pw k) := fun k hk => by
    rw [r3.gpr _ (by revert hk; revert k; decide), r2.gpr _ (by revert hk; revert k; decide), hp1 k hk]
  have hc3 := hc2.of_rest r3 (by decide)
  rw [List.nil_append]
  refine WP.append (highsR_ok h53 (by omega_using [v3, c2])) fun s4 ⟨v4, t4, r4, m4⟩ => ?_
  refine WP.append (foldTop_ok (by rw [r4.gpr _ (by decide), h53]) (by omega_using [t4]))
    fun s5 ⟨v5, t5, r5, m5⟩ => ?_
  refine WP.append (foldTop_ok (by rw [r5.gpr _ (by decide), r4.gpr _ (by decide), h53]) (by omega_using [t5]))
    fun s6 ⟨v6, t6, r6, m6⟩ => ?_
  have hc6 := hc3.of_rest ((r4.mono (ws' := [.r4, .r7, .r8, .r9, .r10, .r11]) (by decide)).trans
    (r5.trans r6)) (by decide)
  refine WP.mono (stores4_ok ho ho4 hc6) fun s7 ⟨v7, f7, r7⟩ => ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans ((r6.mono (by decide)).trans
      (r7.mono (by decide)))))))
  · rwa [m6, m5, m4, m3, m2, u1.mem] at f7
  · rw [v7, pwV_halves]
    have hH4 : val4 (fun k => part true (s3.gpr (pw (4 + k))).toNat) =
        val4 (fun k => part true (s.gpr (pw (4 + k))).toNat) :=
      val4_congr fun k hk => by rw [hp3 _ (by omega_using [hk])]
    have hL1 : val4 (fun k => (s1.gpr (pw k)).toNat) = val4 (fun k => (s.gpr (pw k)).toNat) :=
      val4_congr fun k hk => by rw [hp1 _ (by omega_using [hk])]
    have hP1 : val4 (fun k => part false (s1.gpr (pw (4 + k))).toNat) =
        val4 (fun k => part false (s.gpr (pw (4 + k))).toNat) :=
      val4_congr fun k hk => by rw [hp1 _ (by omega_using [hk])]
    rw [hL1, hP1] at v2
    rw [hH4] at v4
    have hs := parts_sum (fun k => (s.gpr (pw (4 + k))).toNat)
    have b2 := rv4_lt s2; have b4 := rv4_lt s4; have b5 := rv4_lt s5; have b6 := rv4_lt s6
    have hP : P = 2 ^ 255 - 19 := rfl
    rw [e3, rv3] at v4
    generalize val4 (fun k => (s.gpr (pw k)).toNat) = L at *
    generalize val4 (fun k => (s.gpr (pw (4 + k))).toNat) = H at *
    generalize val4 (fun k => part false (s.gpr (pw (4 + k))).toNat) = LO at *
    generalize val4 (fun k => part true (s.gpr (pw (4 + k))).toNat) = HI at *
    have z6 : (s6.gpr .r7).toNat = 0 := by omega_using [v3, c2, l3, e3, t4, v5, t5, v6, t6, b2, b4, b5, b6, v2, v4, hs]
    rw [z6] at v6
    rw [hP]
    omega_using [v5, v6, v2, v4, hs]

/-- `mulR o x y`: `[o] = [x] · [y]` modulo `p`, in registers. -/
theorem mulR_ok {o x y : Nat} (ho : o + 32 ≤ 4096) (hx : x + 32 ≤ 4096) (hy : y + 32 ≤ 4096)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (mulR o x y)) s fun s' =>
      Rest clobR s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := by
  unfold mulR
  refine WP.append (productR_ok hx hy hx4 hy4 hc) fun s1 ⟨hc1, hr1, hm1, hv1⟩ =>
    WP.mono (reduceR_ok ho ho4 hc1) fun s2 ⟨hr2, hf2, hv2⟩ =>
      ⟨hr1.trans (hr2.mono clob_sub), by rw [← hm1]; exact hf2, by rw [hv2, hv1]⟩

end

end VG.Proof.X25519.PPC64LE
