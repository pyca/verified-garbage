module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Product
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.X25519

/-!
# X25519 on PPC64LE: the product reduced

`reduce38 acc o` stores at `o` a number congruent modulo `p` to the eight
words at `acc` (`reduce38_ok`): with `L` and `H` their halves, the words of
`L + lo(38 H)` by the carry chain (`lows_ok`), its carry the top word, then
the high words of `38 H` added one word up (`highs_ok`): `L + 38 H` in four
words `r8`–`r11` and a top word `t ≤ 38` in `r7`. Each `foldTop` adds `38 t`
(`2²⁵⁶ ≡ 38`) and leaves the carry out in `r7` (`foldTop_ok`); after the
first it is 0 or 1, and after the second 0 (`fold_twice`).
-/

-- separate module: its proofs cost more than its imports, and its importer's changes need not
-- re-check them

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P)

/-- The number in `r8`–`r11`. -/
abbrev rv4 (s : State) : Nat := val4 fun i => (s.gpr (wreg i)).toNat

theorem rv4_lt (s : State) : rv4 s < 2 ^ 256 := by
  have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
  have := (s.gpr .r11).isLt
  simp only [rv4, val4, wreg]; simp only [Nat.reduceEqDiff, ↓reduceIte]; omega_arith

section
variable {b : Addr}

/-- A word `x` loaded from `off`, multiplied by 38 (the low word, or with
`hi` the high word), and added to `d` (with the carry in if `e`). -/
def opStep (d : Reg) (off : Nat) (hi e : Bool) : List Instr :=
  [.load .d .r4 .r6 off, if hi then .mulhu .r4 .r4 .r5 else .mul .r4 .r4 .r5,
    if e then .adde d d .r4 else .addc d d .r4]

/-- The part of `38 x` that `opStep` adds. -/
def part (hi : Bool) (x : Nat) : Nat := if hi then x * 38 / 2 ^ 64 else x * 38 % 2 ^ 64

theorem opStep_ok {d : Reg} {off : Nat} (hd4 : d ≠ .r4) {s : State} (hc : Ctx b s)
    (ho : off + 8 ≤ 4096) (ho4 : off % 4 = 0) (h5 : s.gpr .r5 = 38) (hi e : Bool) :
    WP isa (.block (opStep d off hi e)) s fun s' =>
      (s'.gpr d).toNat + 2 ^ 64 * s'.ca.toNat =
        (s.gpr d).toNat + part hi (dw s.mem b off) + (if e then s.ca.toNat else 0) ∧
      s'.ca.toNat ≤ 1 ∧ Rest [.r4, d] s s' ∧ s'.mem = s.mem := by
  have e1 := exec_load_d (s := s) (t := .r4) (n := .r6) (off := off) (by decide) ⟨by omega, ho4⟩
    (by rw [hc.r6]; exact hc.inR ho)
  rw [hc.r6] at e1
  generalize hs1 : s.write .r4 (s.mem.readW (b + BitVec.ofNat 64 off) 64) = s1 at e1
  have g4 : (s1.gpr .r4).toNat = dw s.mem b off := by rw [← hs1, RegUpd.gpr_write_self]; rfl
  have g5 : s1.gpr .r5 = 38 := by rw [← hs1, RegUpd.gpr_write_of_ne _ _ (by decide), h5]
  have gd : s1.gpr d = s.gpr d := by rw [← hs1, RegUpd.gpr_write_of_ne _ _ hd4]
  have hX := dw_lt s.mem b off
  have r1 : Rest [.r4, d] s s1 := by rw [← hs1]; exact (Upd.write _ _ _).rest (by simp)
  have t38 : (38 : BitVec 64).toNat = 38 := rfl
  -- the product's part, into `r4`
  have hpart : ∀ s2 : State, s2 = s1.write .r4 (if hi then BitVec.ofNat 64 ((s1.gpr .r4).toNat *
      (s1.gpr .r5).toNat / 2 ^ 64) else s1.gpr .r4 * s1.gpr .r5) →
      (s2.gpr .r4).toNat = part hi (dw s.mem b off) := by
    intro s2 h2
    rw [h2, RegUpd.gpr_write_self]
    cases hi
    · simp only [Bool.false_eq_true, ↓reduceIte, part]
      rw [BitVec.toNat_mul, g4, g5, t38]
    · simp only [↓reduceIte, part]
      rw [g4, g5, t38, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ex2 : exec (if hi then Instr.mulhu .r4 .r4 .r5 else .mul .r4 .r4 .r5) s1 =
      some (s1.write .r4 (if hi then BitVec.ofNat 64 ((s1.gpr .r4).toNat * (s1.gpr .r5).toNat / 2 ^ 64)
        else s1.gpr .r4 * s1.gpr .r5)) := by
    cases hi <;> rfl
  refine WP.cons e1 (WP.cons ex2 ?_)
  generalize hs2 : s1.write .r4 _ = s2
  have g24 := hpart s2 hs2.symm
  have g2d : s2.gpr d = s.gpr d := by rw [← hs2, RegUpd.gpr_write_of_ne _ _ hd4, gd]
  have c2 : s2.ca = s.ca := by rw [← hs2, RegUpd.ca_write, ← hs1, RegUpd.ca_write]
  have m2 : s2.mem = s.mem := by rw [← hs2, RegUpd.mem_write, ← hs1, RegUpd.mem_write]
  have r2 : Rest [.r4, d] s s2 := r1.trans (by rw [← hs2]; exact (Upd.write _ _ _).rest (by simp))
  cases e
  · refine wp_addc fun s3 u3 => WP.block_nil ⟨?_, u3.ca, r2.trans (u3.rest (by simp)), by rw [u3.mem, m2]⟩
    rw [u3.val, g2d, g24]; simp
  · refine wp_adde fun s3 u3 => WP.block_nil ⟨?_, u3.ca, r2.trans (u3.rest (by simp)), by rw [u3.mem, m2]⟩
    rw [u3.val, g2d, g24, c2]; simp

theorem redLo_eq (acc k : Nat) :
    redLo acc k = .load .d (wreg k) .r6 (acc + 8 * k) :: opStep (wreg k) (acc + 32 + 8 * k) false (k != 0) := by
  unfold redLo opStep; by_cases h : k = 0 <;> simp [h]

theorem redHi_eq (acc k : Nat) :
    redHi acc k = opStep (if k = 3 then .r7 else wreg (k + 1)) (acc + 32 + 8 * k) true (k != 0) := by
  unfold redHi opStep wreg
  by_cases h0 : k = 0
  · simp [h0]
  · by_cases h3 : k = 3 <;> simp [h0, h3]

/-- A load of a doubleword of the working space, as the write it is. -/
theorem ldw_ok {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 8 ≤ 4096) (hd4 : d % 4 = 0)
    {is : List Instr} {Q : State → Prop}
    (k : WP isa (.block is) (s.write t (s.mem.readW (b + BitVec.ofNat 64 d) 64)) Q) :
    WP isa (.block (.load .d t .r6 d :: is)) s Q := by
  have e := exec_load_d (s := s) (t := t) (n := .r6) (off := d) (by decide) ⟨by omega, hd4⟩
    (by rw [hc.r6]; exact hc.inR hd)
  rw [hc.r6] at e
  exact WP.cons e k

/-- Word `k` of `L + lo(38 H)`: `L_k` loaded into `wreg k`, then `opStep`. -/
theorem lstep_ok {acc k : Nat} (hA : acc + 64 ≤ 4096) (hA4 : acc % 4 = 0) (hk : k < 4) {s : State}
    (hc : Ctx b s) (h5 : s.gpr .r5 = 38) :
    WP isa (.block (redLo acc k)) s fun s' =>
      (s'.gpr (wreg k)).toNat + 2 ^ 64 * s'.ca.toNat =
        dw s.mem b (acc + 8 * k) + part false (dw s.mem b (acc + 32 + 8 * k)) +
          (if k != 0 then s.ca.toNat else 0) ∧
      s'.ca.toNat ≤ 1 ∧ Rest [.r4, wreg k] s s' ∧ s'.mem = s.mem := by
  have hw : wreg k ≠ .r4 ∧ wreg k ≠ .r5 ∧ wreg k ≠ .r6 := by revert hk; revert k; decide
  rw [redLo_eq]
  refine ldw_ok hc (by omega) (by omega) ?_
  generalize hs1 : s.write (wreg k) _ = s1
  have hr1 : Rest [.r4, wreg k] s s1 := by rw [← hs1]; exact (Upd.write _ _ _).rest (by simp)
  have hm1 : s1.mem = s.mem := by rw [← hs1, RegUpd.mem_write]
  have hca : s1.ca = s.ca := by rw [← hs1, RegUpd.ca_write]
  have hg : (s1.gpr (wreg k)).toNat = dw s.mem b (acc + 8 * k) := by
    rw [← hs1, RegUpd.gpr_write_self]; rfl
  refine WP.mono (opStep_ok hw.1 (hc.of_rest hr1 (by simp [Ne.symm hw.2.2])) (by omega) (by omega)
    (by rw [hr1.gpr _ (by simp [Ne.symm hw.2.1])]; exact h5) false (k != 0))
    fun s2 ⟨h2, c2, r2, m2⟩ => ⟨?_, c2, hr1.trans r2, by rw [m2, hm1]⟩
  rw [h2, hg, hm1, hca]

/-- The low words: `rv4 + 2²⁵⁶ CA = L + lo(38 H)`. -/
theorem lows_ok {acc : Nat} (hA : acc + 64 ≤ 4096) (hA4 : acc % 4 = 0) {s : State}
    (hc : Ctx b s) (h5 : s.gpr .r5 = 38) :
    WP isa (.block ((List.range 4).flatMap (redLo acc))) s fun s' =>
      rv4 s' + 2 ^ 256 * s'.ca.toNat =
        val4 (fun k => dw s.mem b (acc + 8 * k)) + val4 (fun k => part false (dw s.mem b (acc + 32 + 8 * k))) ∧
      Rest [.r4, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_singleton, List.append_assoc]
  refine WP.append (lstep_ok hA hA4 (k := 0) (by decide) hc h5) fun s1 ⟨v1, c1, r1, m1⟩ => ?_
  have hc1 := hc.of_rest r1 (by decide)
  refine WP.append (lstep_ok hA hA4 (k := 1) (by decide) hc1 (by rw [r1.gpr _ (by decide), h5]))
    fun s2 ⟨v2, c2, r2, m2⟩ => ?_
  have hc2 := hc1.of_rest r2 (by decide)
  refine WP.append (lstep_ok hA hA4 (k := 2) (by decide) hc2
    (by rw [r2.gpr _ (by decide), r1.gpr _ (by decide), h5])) fun s3 ⟨v3', c3, r3, m3⟩ => ?_
  have hc3 := hc2.of_rest r3 (by decide)
  refine WP.mono (lstep_ok hA hA4 (k := 3) (by decide) hc3
    (by rw [r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide), h5]))
    fun s4 ⟨v4, c4, r4, m4⟩ => ⟨?_, ?_, by rw [m4, m3, m2, m1]⟩
  · simp only [m1, m2, m3, show (0 != 0) = false from rfl, show (1 != 0) = true from rfl,
      show (2 != 0) = true from rfl, show (3 != 0) = true from rfl, Bool.false_eq_true,
      ↓reduceIte] at v1 v2 v3' v4
    have e8 : s4.gpr (wreg 0) = s1.gpr (wreg 0) := by
      rw [r4.gpr _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide)]
    have e9 : s4.gpr (wreg 1) = s2.gpr (wreg 1) := by
      rw [r4.gpr _ (by decide), r3.gpr _ (by decide)]
    have e10 : s4.gpr (wreg 2) = s3.gpr (wreg 2) := by rw [r4.gpr _ (by decide)]
    simp only [rv4, val4, e8, e9, e10]
    omega_arith
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      (r4.mono (by decide))))

theorem part_hi_lt (x : Nat) (hx : x < 2 ^ 64) : part true x < 38 := by
  unfold part; simp only [↓reduceIte]; omega

/-- The high words of `38 H`, one word up: into `r9`–`r11` and the top word
`r7`. -/
theorem highs_ok {acc : Nat} (hA : acc + 64 ≤ 4096) (hA4 : acc % 4 = 0) {s : State}
    (hc : Ctx b s) (h5 : s.gpr .r5 = 38) (h7 : (s.gpr .r7).toNat ≤ 1) :
    WP isa (.block ((List.range 4).flatMap (redHi acc))) s fun s' =>
      rv4 s' + 2 ^ 256 * (s'.gpr .r7).toNat = rv4 s + 2 ^ 256 * (s.gpr .r7).toNat +
        2 ^ 64 * val4 (fun k => part true (dw s.mem b (acc + 32 + 8 * k))) ∧
      (s'.gpr .r7).toNat ≤ 39 ∧ Rest [.r4, .r7, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_singleton, List.append_assoc, redHi_eq]
  simp only [show (0 != 0) = false from rfl, show (1 != 0) = true from rfl,
      show (2 != 0) = true from rfl, show (3 != 0) = true from rfl, Nat.reduceEqDiff, ↓reduceIte,
      Nat.reduceAdd, wreg]
  refine WP.append (opStep_ok (d := .r9) (by decide) hc (by omega) (by omega) h5 true false)
    fun s1 ⟨v1, c1, r1, m1⟩ => ?_
  have hc1 := hc.of_rest r1 (by decide)
  refine WP.append (opStep_ok (d := .r10) (by decide) hc1 (by omega) (by omega)
    (by rw [r1.gpr _ (by decide), h5]) true true) fun s2 ⟨v2, c2, r2, m2⟩ => ?_
  have hc2 := hc1.of_rest r2 (by decide)
  refine WP.append (opStep_ok (d := .r11) (by decide) hc2 (by omega) (by omega)
    (by rw [r2.gpr _ (by decide), r1.gpr _ (by decide), h5]) true true) fun s3 ⟨v3', c3, r3, m3⟩ => ?_
  have hc3 := hc2.of_rest r3 (by decide)
  refine WP.mono (opStep_ok (d := .r7) (by decide) hc3 (by omega) (by omega)
    (by rw [r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide), h5]) true true)
    fun s4 ⟨v4, c4, r4, m4⟩ => ?_
  simp only [m1, m2, m3, Bool.false_eq_true, ↓reduceIte] at v1 v2 v3' v4
  have p0 := part_hi_lt _ (dw_lt s.mem b (acc + 32 + 8 * 0))
  have p1 := part_hi_lt _ (dw_lt s.mem b (acc + 32 + 8 * 1))
  have p2 := part_hi_lt _ (dw_lt s.mem b (acc + 32 + 8 * 2))
  have p3 := part_hi_lt _ (dw_lt s.mem b (acc + 32 + 8 * 3))
  have e7 : s3.gpr .r7 = s.gpr .r7 := by
    rw [r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide)]
  rw [e7] at v4
  have hl7 := (s4.gpr .r7).isLt
  refine ⟨?_, by omega, (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
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
  simp only [rv4, val4, wreg, Nat.reduceEqDiff, ↓reduceIte, e8, e9, e10, e11]
  omega_arith

/-- `foldTop`: `rv4 + 2²⁵⁶ r7` becomes `rv4 + 38 r7`, the carry out in `r7`. -/
theorem foldTop_ok {s : State} (h5 : s.gpr .r5 = 38) (h7 : (s.gpr .r7).toNat < 2 ^ 58) :
    WP isa (.block foldTop) s fun s' =>
      rv4 s' + 2 ^ 256 * (s'.gpr .r7).toNat = rv4 s + 38 * (s.gpr .r7).toNat ∧
      (s'.gpr .r7).toNat ≤ 1 ∧ Rest [.r4, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  unfold foldTop
  refine wp_mul fun s1 u1 => wp_addc fun s2 u2 => wp_addze fun s3 u3 => wp_addze fun s4 u4 =>
    wp_addze fun s5 u5 => WP.cons (exec_li (by decide)) (wp_addze fun s7 u7 => WP.block_nil ?_)
  have t38 : (38 : BitVec 64).toNat = 38 := rfl
  have e1 : (s1.gpr .r4).toNat = (s.gpr .r7).toNat * 38 := by
    rw [u1.gpr, h5, BitVec.toNat_mul, t38, Nat.mod_eq_of_lt (by omega)]
  have v2 := u2.val; have v3 := u3.val; have v4 := u4.val; have v5 := u5.val; have v7 := u7.val
  rw [u1.other _ (by decide), e1] at v2
  rw [u2.other _ (by decide), u1.other _ (by decide)] at v3
  rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)] at v4
  rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)] at v5
  rw [RegUpd.gpr_write_self, RegUpd.ca_write] at v7
  have c5 := u5.ca
  have l7 := (s7.gpr .r7).isLt
  have x : (BitVec.ofNat 64 0).toNat = 0 := rfl
  rw [x] at v7
  have e8 : s7.gpr .r8 = s2.gpr .r8 := by
    rw [u7.other _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide)]
  have e9 : s7.gpr .r9 = s3.gpr .r9 := by
    rw [u7.other _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide)]
  have e10 : s7.gpr .r10 = s4.gpr .r10 := by
    rw [u7.other _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), u5.other _ (by decide)]
  have e11 : s7.gpr .r11 = s5.gpr .r11 := by
    rw [u7.other _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide)]
  refine ⟨?_, by omega, ?_, by rw [u7.mem, RegUpd.mem_write, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]⟩
  · simp only [rv4, val4, wreg, Nat.reduceEqDiff, ↓reduceIte, e8, e9, e10, e11]
    omega_arith
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (((Upd.write _ _ _).rest (by decide)).trans
      (u7.rest (by decide)))))))

/-- The stores of `r8`–`r11` at `o`. -/
theorem stores4_ok {o : Nat} (ho : o + 32 ≤ 4096) (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block ((List.range 4).map fun k => .store .d (wreg k) .r6 (o + 8 * k))) s fun s' =>
      V s'.mem b o = rv4 s ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧ Rest [] s s' := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append]
  refine sd0_ok hc (by omega) (by omega) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest []) (by decide)
  refine sd0_ok hc1 (by omega) (by omega) fun s2 u2 => ?_
  have hc2 := hc1.of_rest (u2.rest []) (by decide)
  refine sd0_ok hc2 (by omega) (by omega) fun s3 u3 => ?_
  have hc3 := hc2.of_rest (u3.rest []) (by decide)
  refine sd0_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ⟨?_, ?_, ?_⟩
  · have g3 : s3.gpr = s.gpr := by rw [u3.gpr, u2.gpr, u1.gpr]
    have g2 : s2.gpr = s.gpr := by rw [u2.gpr, u1.gpr]
    have g1 : s1.gpr = s.gpr := u1.gpr
    rw [V_eq4, u4.mem, u3.mem, u2.mem, u1.mem, g3, g2, g1]
    simp only [val4, ew, rv4, wreg, Nat.reduceEqDiff, ↓reduceIte, Nat.mul_zero, Nat.add_zero,
      Nat.mul_one, Nat.reduceMul]
    rw [dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self,
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_self, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self, dw_write_self]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
    have hk : ∀ k < 4, (⟨b + BitVec.ofNat 64 (o + 8 * k), 8⟩ : Region).Sub ⟨b + BitVec.ofNat 64 o, 32⟩ :=
      fun k hk => Offset.sub _ (by omega) (by omega)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega)) |>.writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))
  · exact (u1.rest _).trans ((u2.rest _).trans ((u3.rest _).trans (u4.rest _)))

/-- The low and high parts of `38 H` are `38 H`. -/
theorem parts_sum (H : Nat → Nat) :
    val4 (fun k => part false (H k)) + 2 ^ 64 * val4 (fun k => part true (H k)) = 38 * val4 H := by
  have h : ∀ x, part false x + 2 ^ 64 * part true x = x * 38 := fun x => by
    simp only [part, Bool.false_eq_true, ↓reduceIte]; exact Nat.mod_add_div _ _
  have := h (H 0); have := h (H 1); have := h (H 2); have := h (H 3)
  simp only [val4]; omega_arith

/-- The eight words at `acc` are its halves. -/
theorem accW_halves (acc : Nat) (m : Mem) (b : Addr) :
    accW acc m b 8 = val4 (fun k => dw m b (acc + 8 * k)) + 2 ^ 256 * val4 (fun k => dw m b (acc + 32 + 8 * k)) := by
  simp only [accW, val4, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reducePow,
    Nat.pow_zero, Nat.zero_add, Nat.reduceAdd, Nat.add_assoc]
  omega_arith

/-- `reduce38 acc o`: a number congruent to the product at `acc`, at `o`. -/
theorem reduce38_ok {acc o : Nat} (hA : acc + 64 ≤ 4096) (hA4 : acc % 4 = 0) (ho : o + 32 ≤ 4096)
    (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (reduce38 acc o)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      V s'.mem b o % P = accW acc s.mem b 8 % P := by
  unfold reduce38
  simp only [List.cons_append, List.append_assoc]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  refine WP.append (lows_ok hA hA4 hc1 (by rw [u1.gpr]; rfl)) fun s2 ⟨v2, r2, m2⟩ => ?_
  have hc2 := hc1.of_rest r2 (by decide)
  refine WP.cons (exec_li (by decide)) (wp_addze fun s3 u3 => ?_)
  have v3 := u3.val
  rw [RegUpd.gpr_write_self, RegUpd.ca_write] at v3
  have z : (BitVec.ofNat 64 0).toNat = 0 := rfl
  rw [z] at v3
  have c2 : s2.ca.toNat ≤ 1 := Bool.toNat_le _
  have l3 := (s3.gpr .r7).isLt
  have e3 : (s3.gpr .r7).toNat = s2.ca.toNat := by omega
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
  have hc3 := hc2.of_rest r3 (by decide)
  rw [List.nil_append]
  refine WP.append (highs_ok hA hA4 hc3 h53 (by omega)) fun s4 ⟨v4, t4, r4, m4⟩ => ?_
  refine WP.append (foldTop_ok (by rw [r4.gpr _ (by decide), h53]) (by omega))
    fun s5 ⟨v5, t5, r5, m5⟩ => ?_
  refine WP.append (foldTop_ok (by rw [r5.gpr _ (by decide), r4.gpr _ (by decide), h53]) (by omega))
    fun s6 ⟨v6, t6, r6, m6⟩ => ?_
  have hc6 := hc3.of_rest ((r4.mono (ws' := [.r4, .r7, .r8, .r9, .r10, .r11]) (by decide)).trans
    (r5.trans r6)) (by decide)
  refine WP.mono (stores4_ok ho ho4 hc6) fun s7 ⟨v7, f7, r7⟩ => ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans ((r6.mono (by decide)).trans
      (r7.mono (by decide)))))))
  · rwa [m6, m5, m4, m3, m2, u1.mem] at f7
  · rw [v7, accW_halves]
    rw [m3, m2, u1.mem] at v4
    rw [u1.mem] at v2
    have hs := parts_sum (fun k => dw s.mem b (acc + 32 + 8 * k))
    have b2 := rv4_lt s2; have b4 := rv4_lt s4; have b5 := rv4_lt s5; have b6 := rv4_lt s6
    have hP : P = 2 ^ 255 - 19 := rfl
    rw [e3, rv3] at v4
    generalize val4 (fun k => dw s.mem b (acc + 8 * k)) = L at *
    generalize val4 (fun k => dw s.mem b (acc + 32 + 8 * k)) = H at *
    generalize val4 (fun k => part false (dw s.mem b (acc + 32 + 8 * k))) = LO at *
    generalize val4 (fun k => part true (dw s.mem b (acc + 32 + 8 * k))) = HI at *
    have z6 : (s6.gpr .r7).toNat = 0 := by omega
    rw [z6] at v6
    rw [hP]
    omega

end

end VG.Proof.X25519.PPC64LE
