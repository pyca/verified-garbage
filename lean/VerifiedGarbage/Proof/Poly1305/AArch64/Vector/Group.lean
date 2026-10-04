import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Split
import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Macs
import VerifiedGarbage.Proof.Poly1305.Pair

/-!
# Poly1305 on AArch64 in AdvSIMD: a group of four blocks

Untrusted: everything here is checked by Lean. `group R S` leaves in lane `e`
of the accumulator the carried sum of the products of `(H + m_e)` and of
`m_(2+e)` by the multipliers in words `e` and `2 + e` of `R` (and `5 R` in
`S`): `(A + m₀) ρ₀ + m₂ ρ₂` and `(B + m₁) ρ₁ + m₃ ρ₃`.
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)

theorem iV_ne_hV : ∀ i < 5, ∀ j < 5, iV i ≠ hV j := by decide

/-- Only the operand vectors change. -/
structure IKeep (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : ∀ r, (∀ i < 5, r ≠ iV i) → t.v r = s.v r

theorem narrow_ok (s : State) :
    WP isa (.block narrow) s fun t =>
      (∀ i < 5, ∀ c < 4, wd (t.v (iV i)) c = ln (s.v (iV i)) (c % 2) % 2 ^ 32) ∧ IKeep s t := by
  simp only [narrow, List.range, List.range.loop, List.map]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_nil_iff.mpr ⟨fun i hi c hc => ?_, ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩⟩
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
      vstep <;> exact wd_uzp_self _ hc
  · simp only [RegUpd.gpr_setV]
  · simp only [RegUpd.mem_setV]
  · simp only [RegUpd.rd_setV]
  · simp only [RegUpd.wr_setV]
  · simp only [RegUpd.sp_setV]
  · have := hr 0 (by decide); have := hr 1 (by decide); have := hr 2 (by decide)
    have := hr 3 (by decide); have := hr 4 (by decide)
    simp (disch := assumption) only [RegUpd.v_setV_of_ne]

theorem addH_ok (s : State) :
    WP isa (.block addH) s fun t =>
      (∀ i < 5, ∀ e < 2, ln (t.v (iV i)) e = (ln (s.v (iV i)) e + ln (s.v (hV i)) e) % 2 ^ 64) ∧
        IKeep s t := by
  simp only [addH, List.range, List.range.loop, List.map]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_nil_iff.mpr ⟨fun i hi e he => ?_, ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩⟩
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
      vstep <;> exact ln_add _ _ he
  · simp only [RegUpd.gpr_setV]
  · simp only [RegUpd.mem_setV]
  · simp only [RegUpd.rd_setV]
  · simp only [RegUpd.wr_setV]
  · simp only [RegUpd.sp_setV]
  · have := hr 0 (by decide); have := hr 1 (by decide); have := hr 2 (by decide)
    have := hr 3 (by decide); have := hr 4 (by decide)
    simp (disch := assumption) only [RegUpd.v_setV_of_ne]

/-- What the carry keeps: all but the accumulator, the products and the temporary. -/
structure CKeep (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : ∀ r, (∀ i < 5, r ≠ hV i ∧ r ≠ dV i ∧ r ≠ iV i) → t.v r = s.v r

theorem carry_ok (s : State) (hm : ∀ e < 2, ln (s.v maskV) e = 2 ^ 26 - 1) :
    WP isa (.block carry) s fun t =>
      ((∀ k < 5, ∀ e < 2, ln (s.v (dV k)) e < 2 ^ 62) →
        ∀ i < 5, ∀ e < 2, ln (t.v (hV i)) e = Pair.carry (fun k => ln (s.v (dV k)) e) i) ∧
        CKeep s t := by
  simp only [carry, carry1, List.cons_append, List.nil_append]
  iterate 23
    refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
    vstep
  refine WP.block_nil_iff.mpr ⟨fun hd i hi e he => ?_, ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩⟩
  · have hM := hm e he
    have d0 := hd 0 (by decide) e he; have d1 := hd 1 (by decide) e he
    have d2 := hd 2 (by decide) e he; have d3 := hd 3 (by decide) e he
    have d4 := hd 4 (by decide) e he
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
      vstep <;>
      simp only [ln_and_mask _ _ hM, ln_add _ _ he, ln_ushr _ _ _ he, ln_shl _ _ _ he] <;>
      simp only [Pair.carry, Pair.h0b, Pair.h3b, Pair.d1a, Pair.d2a, Pair.d4a] <;>
      simp (disch := omega) only [Nat.mod_eq_of_lt]
  · simp only [RegUpd.gpr_setV]
  · simp only [RegUpd.mem_setV]
  · simp only [RegUpd.rd_setV]
  · simp only [RegUpd.wr_setV]
  · simp only [RegUpd.sp_setV]
  · have h0 := hr 0 (by decide); have h1 := hr 1 (by decide); have h2 := hr 2 (by decide)
    have h3 := hr 3 (by decide); have h4 := hr 4 (by decide)
    obtain ⟨_, _, _⟩ := h0; obtain ⟨_, _, _⟩ := h1; obtain ⟨_, _, _⟩ := h2
    obtain ⟨_, _, _⟩ := h3; obtain ⟨_, _, _⟩ := h4
    simp (disch := assumption) only [RegUpd.v_setV_of_ne]

/-! ## Products -/

/-- A row of `prodHi`/`prodLo`. -/
abbrev rowL (hi fresh : Bool) (R S : Nat → VReg) (i : Nat) : List Instr :=
  (List.range 5).map (mac hi fresh i (mulV R S i))

theorem prodHi_eq (R S : Nat → VReg) : prodHi R S = rowL true true R S 0 ++ (rowL true false R S 1 ++
    (rowL true false R S 2 ++ (rowL true false R S 3 ++ rowL true false R S 4))) := rfl

theorem prodLo_eq (R S : Nat → VReg) : prodLo R S = rowL false false R S 0 ++ (rowL false false R S 1 ++
    (rowL false false R S 2 ++ (rowL false false R S 3 ++ rowL false false R S 4))) := rfl

theorem term_keep {s t : State} (h : MKeep s t) {M : Nat → VReg} (hM : ∀ k < 5, ∀ j < 5, M k ≠ dV j)
    (hi : Bool) {i : Nat} (hi5 : i < 5) {k : Nat} (hk : k < 5) (e : Nat) :
    term t hi i M k e = term s hi i M k e := by
  have h1 : t.v (iV i) = s.v (iV i) := h.v _ fun j hj => (dV_ne_iV j hj i hi5).symm
  have h2 : t.v (M k) = s.v (M k) := h.v _ fun j hj => hM k hk j hj
  simp only [term, h1, h2]

/-- Multipliers in registers other than the products. -/
abbrev MulOk (R S : Nat → VReg) : Prop := ∀ i < 5, ∀ k < 5, ∀ j < 5, mulV R S i k ≠ dV j

theorem prodHi_ok {R S : Nat → VReg} (hRS : MulOk R S) (s : State)
    (hb : ∀ i < 5, ∀ k < 5, ∀ e < 2, term s true i (mulV R S i) k e < 2 ^ 59) :
    WP isa (.block (prodHi R S)) s fun t =>
      (∀ k < 5, ∀ e < 2, ln (t.v (dV k)) e = term s true 0 (mulV R S 0) k e + term s true 1 (mulV R S 1) k e +
        term s true 2 (mulV R S 2) k e + term s true 3 (mulV R S 3) k e + term s true 4 (mulV R S 4) k e) ∧
        MKeep s t := by
  rw [prodHi_eq]
  refine WP.block_append (WP.mono (row_ok true true (by decide) (hRS 0 (by decide)) s) fun t0 ⟨h0, k0⟩ => ?_)
  refine WP.block_append (WP.mono (row_ok true false (by decide) (hRS 1 (by decide)) t0) fun t1 ⟨h1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (row_ok true false (by decide) (hRS 2 (by decide)) t1) fun t2 ⟨h2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (row_ok true false (by decide) (hRS 3 (by decide)) t2) fun t3 ⟨h3, k3⟩ => ?_)
  refine WP.mono (row_ok true false (by decide) (hRS 4 (by decide)) t3) fun t4 ⟨h4, k4⟩ =>
    ⟨fun k hk e he => ?_, k0.trans (k1.trans (k2.trans (k3.trans k4)))⟩
  have k01 := k0.trans k1
  have k02 := k01.trans k2
  have k03 := k02.trans k3
  rw [h4 k hk e he, h3 k hk e he, h2 k hk e he, h1 k hk e he, h0 k hk e he,
    term_keep k0 (hRS 1 (by decide)) _ (by decide) hk, term_keep k01 (hRS 2 (by decide)) _ (by decide) hk,
    term_keep k02 (hRS 3 (by decide)) _ (by decide) hk, term_keep k03 (hRS 4 (by decide)) _ (by decide) hk]
  have := hb 0 (by decide) k hk e he; have := hb 1 (by decide) k hk e he
  have := hb 2 (by decide) k hk e he; have := hb 3 (by decide) k hk e he
  have := hb 4 (by decide) k hk e he
  simp only [ite_true, Bool.false_eq_true, ite_false]
  simp (disch := omega) only [Nat.mod_eq_of_lt, Nat.zero_add]

theorem prodLo_ok {R S : Nat → VReg} (hRS : MulOk R S) (s : State) :
    WP isa (.block (prodLo R S)) s fun t =>
      ((∀ i < 5, ∀ k < 5, ∀ e < 2, term s false i (mulV R S i) k e < 2 ^ 59) →
        (∀ k < 5, ∀ e < 2, ln (s.v (dV k)) e < 2 ^ 62) →
        ∀ k < 5, ∀ e < 2, ln (t.v (dV k)) e = ln (s.v (dV k)) e + (term s false 0 (mulV R S 0) k e +
          term s false 1 (mulV R S 1) k e + term s false 2 (mulV R S 2) k e +
          term s false 3 (mulV R S 3) k e + term s false 4 (mulV R S 4) k e)) ∧ MKeep s t := by
  rw [prodLo_eq]
  refine WP.block_append (WP.mono (row_ok false false (by decide) (hRS 0 (by decide)) s) fun t0 ⟨h0, k0⟩ => ?_)
  refine WP.block_append (WP.mono (row_ok false false (by decide) (hRS 1 (by decide)) t0) fun t1 ⟨h1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (row_ok false false (by decide) (hRS 2 (by decide)) t1) fun t2 ⟨h2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (row_ok false false (by decide) (hRS 3 (by decide)) t2) fun t3 ⟨h3, k3⟩ => ?_)
  refine WP.mono (row_ok false false (by decide) (hRS 4 (by decide)) t3) fun t4 ⟨h4, k4⟩ =>
    ⟨fun hb hd k hk e he => ?_, k0.trans (k1.trans (k2.trans (k3.trans k4)))⟩
  have k01 := k0.trans k1
  have k02 := k01.trans k2
  have k03 := k02.trans k3
  rw [h4 k hk e he, h3 k hk e he, h2 k hk e he, h1 k hk e he, h0 k hk e he,
    term_keep k0 (hRS 1 (by decide)) _ (by decide) hk, term_keep k01 (hRS 2 (by decide)) _ (by decide) hk,
    term_keep k02 (hRS 3 (by decide)) _ (by decide) hk, term_keep k03 (hRS 4 (by decide)) _ (by decide) hk]
  have := hb 0 (by decide) k hk e he; have := hb 1 (by decide) k hk e he
  have := hb 2 (by decide) k hk e he; have := hb 3 (by decide) k hk e he
  have := hb 4 (by decide) k hk e he; have := hd k hk e he
  simp only [Bool.false_eq_true, ite_false]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  omega

/-! ## The group -/

/-- The multipliers `R` (words `y c i`, below `2²⁷`) and `S` (`5 y`, limbs 1–4),
in registers the group does not write. -/
structure Mults (s : State) (R S : Nat → VReg) (y : Nat → Nat → Nat) : Prop where
  r : ∀ i < 5, ∀ c < 4, wd (s.v (R i)) c = y c i
  s5 : ∀ j < 5, 1 ≤ j → ∀ c < 4, wd (s.v (S j)) c = 5 * y c j
  lt : ∀ c < 4, ∀ i < 5, y c i < 2 ^ 27
  regR : ∀ i < 5, ∀ j < 5, R i ≠ iV j ∧ R i ≠ dV j ∧ R i ≠ hV j
  regS : ∀ i < 5, 1 ≤ i → ∀ j < 5, S i ≠ iV j ∧ S i ≠ dV j ∧ S i ≠ hV j

theorem Mults.mulOk {s : State} {R S : Nat → VReg} {y : Nat → Nat → Nat} (h : Mults s R S y) : MulOk R S := by
  intro i hi k hk j hj
  simp only [mulV]
  split
  · exact (h.regR (k - i) (by omega) j hj).2.1
  · exact (h.regS (k + 5 - i) (by omega) (by omega) j hj).2.1

theorem Mults.mul_regs {s : State} {R S : Nat → VReg} {y : Nat → Nat → Nat} (h : Mults s R S y)
    {i k : Nat} (hi : i < 5) (hk : k < 5) : ∀ j < 5, mulV R S i k ≠ iV j ∧ mulV R S i k ≠ dV j ∧ mulV R S i k ≠ hV j := by
  intro j hj
  simp only [mulV]
  split
  · exact h.regR (k - i) (by omega) j hj
  · exact h.regS (k + 5 - i) (by omega) (by omega) j hj

theorem Mults.wd_mul {s : State} {R S : Nat → VReg} {y : Nat → Nat → Nat} (h : Mults s R S y)
    {i k c : Nat} (hi : i < 5) (hk : k < 5) (hc : c < 4) : wd (s.v (mulV R S i k)) c = Pair.mulL (y c) i k := by
  simp only [mulV, Pair.mulL]
  split
  · exact h.r _ (by omega) c hc
  · exact h.s5 _ (by omega) (by omega) c hc

theorem Mults.mulL_lt {s : State} {R S : Nat → VReg} {y : Nat → Nat → Nat} (h : Mults s R S y)
    {i k c : Nat} (hk : k < 5) (hc : c < 4) : Pair.mulL (y c) i k < 5 * 2 ^ 27 := by
  simp only [Pair.mulL]
  split
  · have := h.lt c hc (k - i) (by omega); omega
  · have := h.lt c hc (k + 5 - i) (by omega); omega

/-- `Mults` holds of a state with the same multiplier registers. -/
theorem Mults.of_v {s t : State} {R S : Nat → VReg} {y : Nat → Nat → Nat} (h : Mults s R S y)
    (hv : ∀ r, (∀ j < 5, r ≠ iV j ∧ r ≠ dV j ∧ r ≠ hV j) → t.v r = s.v r) : Mults t R S y where
  r i hi c hc := by rw [hv _ (h.regR i hi)]; exact h.r i hi c hc
  s5 j hj h1 c hc := by rw [hv _ (h.regS j hj h1)]; exact h.s5 j hj h1 c hc
  lt := h.lt
  regR := h.regR
  regS := h.regS

/-- The address of block `j` of a group. -/
abbrev gAddr (s : State) (j : Nat) : Addr := s.gpr .x2 + BitVec.ofNat 64 (16 * j)

/-- The limbs of block `j` of the group. -/
abbrev gblk (s : State) (j : Nat) : Nat → Nat := blk (blo s.mem (gAddr s j)) (bhi s.mem (gAddr s j))

/-- Lane `e` of the accumulator. -/
abbrev hl (s : State) (e : Nat) : Nat → Nat := fun i => ln (s.v (hV i)) e

/-- What a group keeps. -/
structure GKeep (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : ∀ r, (∀ i < 5, r ≠ hV i ∧ r ≠ dV i ∧ r ≠ iV i) → t.v r = s.v r

/-- Lane `e` of the products of a group: `(H + m_e) ρ_e + m_(2+e) ρ_(2+e)`. -/
def gprod (H : Nat → Nat) (y : Nat → Nat → Nat) (b : Nat → Nat → Nat) (e k : Nat) : Nat :=
  Pair.prod (b (2 + e)) (y (2 + e)) k + Pair.prod (fun i => H i + b e i) (y e) k

theorem group_ok {s : State} {R S : Nat → VReg} {y : Nat → Nat → Nat} (hmul : Mults s R S y)
    (hm : ∀ e < 2, ln (s.v maskV) e = 2 ^ 26 - 1) (hpd : ∀ e < 2, ln (s.v padV) e = 2 ^ 24)
    (hr : ∀ j < 4, InRegions (s.rd ++ s.wr) (gAddr s j) 16) :
    WP isa (.block (group R S)) s fun t =>
      ((∀ e < 2, ∀ i < 5, hl s e i < 2 ^ 27) →
        ∀ e < 2, ∀ i < 5, hl t e i = Pair.carry (gprod (hl s e) y (gblk s) e) i ∧ hl t e i < 2 ^ 27) ∧
        GKeep s t := by
  have mok := hmul.mulOk
  have hmV : ∀ j < 5, maskV ≠ iV j ∧ maskV ≠ dV j ∧ maskV ≠ hV j := by decide
  have hpV : ∀ j < 5, padV ≠ iV j ∧ padV ≠ dV j ∧ padV ≠ hV j := by decide
  have hI : ∀ k < 5, ∀ j < 5, hV k ≠ iV j := by decide
  have hD : ∀ k < 5, ∀ j < 5, hV k ≠ dV j := by decide
  have dI : ∀ k < 5, ∀ j < 5, dV k ≠ iV j := by decide
  have aHi : ∀ e < 2, bAddr s 32 e = gAddr s (2 + e) := fun e _ => by
    simp only [bAddr, gAddr]; congr 2; omega
  have aLo : ∀ e, bAddr s 0 e = gAddr s e := fun e => by
    simp only [bAddr, gAddr, Nat.zero_add]
  have lt32 : ∀ x : Nat, x < 2 ^ 28 → x < 2 ^ 32 := fun x h => Nat.lt_of_lt_of_le h (by decide)
  simp only [group, List.append_assoc]
  -- the second pair of blocks
  refine WP.block_append (WP.mono (split_ok (by decide) (by decide) hm hpd
    (fun e he => by rw [aHi e he]; exact hr _ (by omega))) fun s1 ⟨l1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (narrow_ok s1) fun s2 ⟨w2, k2⟩ => ?_)
  have v12 : ∀ r, (∀ j < 5, r ≠ iV j) → s2.v r = s.v r := fun r h =>
    (k2.v r h).trans (k1.v r h)
  have m2 : Mults s2 R S y := hmul.of_v fun r h => v12 r fun j hj => (h j hj).1
  have tHi : ∀ i < 5, ∀ k < 5, ∀ e < 2, term s2 true i (mulV R S i) k e =
      gblk s (2 + e) i * Pair.mulL (y (2 + e)) i k := by
    intro i hi k hk e he
    simp only [term, hp, ite_true]
    rw [w2 i hi _ (by omega), show (2 + e) % 2 = e by omega, l1 i hi e he, aHi e he,
      Nat.mod_eq_of_lt (lt32 _ (Nat.lt_of_lt_of_le (blk_lt _ (vdword _ 1).isLt i hi) (by decide))),
      m2.wd_mul hi hk (by omega)]
  refine WP.block_append (WP.mono (prodHi_ok mok s2 fun i hi k hk e he => by
    rw [tHi i hi k hk e he]
    calc _ < 2 ^ 26 * (5 * 2 ^ 27) := Nat.mul_lt_mul'' (blk_lt _ (vdword _ 1).isLt i hi)
          (hmul.mulL_lt hk (by omega))
      _ ≤ 2 ^ 59 := by decide) fun s3 ⟨d3, k3⟩ => ?_)
  -- the first pair of blocks, plus the accumulator
  have g3 : s3.gpr = s.gpr := k3.gpr.trans (k2.gpr.trans k1.gpr)
  have mm3 : s3.mem = s.mem := k3.mem.trans (k2.mem.trans k1.mem)
  have rd3 : s3.rd = s.rd := k3.rd.trans (k2.rd.trans k1.rd)
  have wr3 : s3.wr = s.wr := k3.wr.trans (k2.wr.trans k1.wr)
  have v3 : ∀ r, (∀ j < 5, r ≠ iV j ∧ r ≠ dV j) → s3.v r = s.v r := fun r h =>
    (k3.v r fun j hj => (h j hj).2).trans (v12 r fun j hj => (h j hj).1)
  have b3 : ∀ e, bAddr s3 0 e = gAddr s e := fun e => by simp only [bAddr, gAddr, g3, Nat.zero_add]
  refine WP.block_append (WP.mono (split_ok (by decide) (by decide)
    (fun e he => by rw [v3 _ fun j hj => ⟨(hmV j hj).1, (hmV j hj).2.1⟩]; exact hm e he)
    (fun e he => by rw [v3 _ fun j hj => ⟨(hpV j hj).1, (hpV j hj).2.1⟩]; exact hpd e he)
    (fun e he => by rw [b3, rd3, wr3]; exact hr _ (by omega))) fun s4 ⟨l4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (addH_ok s4) fun s5 ⟨a5, k5⟩ => ?_)
  refine WP.block_append (WP.mono (narrow_ok s5) fun s6 ⟨w6, k6⟩ => ?_)
  have v46 : ∀ r, (∀ j < 5, r ≠ iV j) → s6.v r = s4.v r := fun r h => (k6.v r h).trans (k5.v r h)
  have v36 : ∀ r, (∀ j < 5, r ≠ iV j) → s6.v r = s3.v r := fun r h => (v46 r h).trans (k4.v r h)
  have v06 : ∀ r, (∀ j < 5, r ≠ iV j ∧ r ≠ dV j) → s6.v r = s.v r := fun r h =>
    (v36 r fun j hj => (h j hj).1).trans (v3 r h)
  have h4 : ∀ i < 5, ∀ e < 2, ln (s4.v (hV i)) e = hl s e i := fun i hi e he => by
    rw [k4.v _ fun j hj => hI i hi j hj, v3 _ fun j hj => ⟨hI i hi j hj, hD i hi j hj⟩]
  have m6 : Mults s6 R S y := hmul.of_v fun r h => v06 r fun j hj => ⟨(h j hj).1, (h j hj).2.1⟩
  have opLo : (∀ e < 2, ∀ i < 5, hl s e i < 2 ^ 27) → ∀ i < 5, ∀ e < 2, wd (s6.v (iV i)) (hp false + e) = hl s e i + gblk s e i := by
    intro hH i hi e he
    have hb : gblk s e i < 2 ^ 26 := blk_lt _ (vdword _ 1).isLt i hi
    have hb' : blk (blo s.mem (gAddr s e)) (bhi s.mem (gAddr s e)) i < 2 ^ 26 := hb
    have hh := hH e he i hi
    simp only [hp, Bool.false_eq_true, ite_false, Nat.zero_add]
    rw [w6 i hi _ (by omega), Nat.mod_eq_of_lt he, a5 i hi e he, l4 i hi e he, h4 i hi e he, b3,
      mm3, show (blk (blo s.mem (gAddr s e)) (bhi s.mem (gAddr s e)) i + hl s e i) % 2 ^ 64 =
        blk (blo s.mem (gAddr s e)) (bhi s.mem (gAddr s e)) i + hl s e i from Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (lt32 _ (by omega)), Nat.add_comm]
  have tLo : (∀ e < 2, ∀ i < 5, hl s e i < 2 ^ 27) → ∀ i < 5, ∀ k < 5, ∀ e < 2, term s6 false i (mulV R S i) k e =
      (hl s e i + gblk s e i) * Pair.mulL (y e) i k := by
    intro hH i hi k hk e he
    simp only [term]
    rw [opLo hH i hi e he, m6.wd_mul hi hk (by simp only [hp, Bool.false_eq_true, ite_false]; omega)]
    simp only [hp, Bool.false_eq_true, ite_false, Nat.zero_add]
  have d6 : ∀ k < 5, ∀ e < 2, ln (s6.v (dV k)) e = Pair.prod (gblk s (2 + e)) (y (2 + e)) k := by
    intro k hk e he
    rw [v36 _ fun j hj => dI k hk j hj, d3 k hk e he, tHi 0 (by decide) k hk e he,
      tHi 1 (by decide) k hk e he, tHi 2 (by decide) k hk e he, tHi 3 (by decide) k hk e he,
      tHi 4 (by decide) k hk e he]
    rfl
  have bLo : (∀ e < 2, ∀ i < 5, hl s e i < 2 ^ 27) → ∀ i < 5, ∀ k < 5, ∀ e < 2, (hl s e i + gblk s e i) * Pair.mulL (y e) i k < 2 ^ 58 := by
    intro hH i hi k hk e he
    have hb : gblk s e i < 2 ^ 26 := blk_lt _ (vdword _ 1).isLt i hi
    have hh := hH e he i hi
    calc _ < 2 ^ 28 * (5 * 2 ^ 27) := Nat.mul_lt_mul'' (by omega) (hmul.mulL_lt hk (by omega))
      _ ≤ 2 ^ 58 := by decide
  have pHi : ∀ k < 5, ∀ e < 2, Pair.prod (gblk s (2 + e)) (y (2 + e)) k < 2 ^ 59 := by
    intro k hk e he
    have b : ∀ i < 5, gblk s (2 + e) i * Pair.mulL (y (2 + e)) i k < 2 ^ 56 := fun i hi =>
      calc _ < 2 ^ 26 * (5 * 2 ^ 27) := Nat.mul_lt_mul'' (blk_lt _ (vdword _ 1).isLt i hi)
            (hmul.mulL_lt hk (by omega))
        _ ≤ 2 ^ 56 := by decide
    have := b 0 (by decide); have := b 1 (by decide); have := b 2 (by decide)
    have := b 3 (by decide); have := b 4 (by decide)
    simp only [Pair.prod]; omega
  refine WP.block_append (WP.mono (prodLo_ok mok s6) fun s7 ⟨d7, k7⟩ => ?_)
  have hD7 : (∀ e < 2, ∀ i < 5, hl s e i < 2 ^ 27) → ∀ k < 5, ∀ e < 2, ln (s7.v (dV k)) e = gprod (hl s e) y (gblk s) e k := by
    intro hH k hk e he
    rw [d7 (fun i hi k hk e he => by rw [tLo hH i hi k hk e he]; exact Nat.lt_trans (bLo hH i hi k hk e he) (by decide))
      (fun k hk e he => by rw [d6 k hk e he]; exact Nat.lt_trans (pHi k hk e he) (by decide)) k hk e he,
      d6 k hk e he, tLo hH 0 (by decide) k hk e he, tLo hH 1 (by decide) k hk e he,
      tLo hH 2 (by decide) k hk e he, tLo hH 3 (by decide) k hk e he, tLo hH 4 (by decide) k hk e he]
    rfl
  have mask7 : ∀ e < 2, ln (s7.v maskV) e = 2 ^ 26 - 1 := fun e he => by
    rw [k7.v _ fun j hj => (hmV j hj).2.1, v06 _ fun j hj => ⟨(hmV j hj).1, (hmV j hj).2.1⟩]
    exact hm e he
  have gB : (∀ e < 2, ∀ i < 5, hl s e i < 2 ^ 27) → ∀ e < 2, ∀ k < 5, gprod (hl s e) y (gblk s) e k < 2 ^ 62 := fun hH e he k hk => by
    have := pHi k hk e he
    have b : ∀ i < 5, (hl s e i + gblk s e i) * Pair.mulL (y e) i k < 2 ^ 58 := fun i hi =>
      bLo hH i hi k hk e he
    have := b 0 (by decide); have := b 1 (by decide); have := b 2 (by decide)
    have := b 3 (by decide); have := b 4 (by decide)
    simp only [gprod, Pair.prod] at *; omega
  refine WP.mono (carry_ok s7 mask7) fun t ⟨c, k8⟩ => ⟨fun hH e he i hi => ?_, ?_⟩
  · have eq := (c (fun k hk e he => by rw [hD7 hH k hk e he]; exact gB hH e he k hk) i hi e he).trans
      (Pair.carry_congr (fun k hk => hD7 hH k hk e he) i)
    exact ⟨eq, by rw [show hl t e i = _ from eq]; exact Pair.carry_lt (gB hH e he) i hi⟩
  · refine ⟨k8.gpr.trans (k7.gpr.trans (k6.gpr.trans (k5.gpr.trans (k4.gpr.trans g3)))),
      k8.mem.trans (k7.mem.trans (k6.mem.trans (k5.mem.trans (k4.mem.trans mm3)))),
      k8.rd.trans (k7.rd.trans (k6.rd.trans (k5.rd.trans (k4.rd.trans rd3)))),
      k8.wr.trans (k7.wr.trans (k6.wr.trans (k5.wr.trans (k4.wr.trans wr3)))),
      k8.sp.trans (k7.sp.trans (k6.sp.trans (k5.sp.trans (k4.sp.trans (k3.sp.trans (k2.sp.trans k1.sp)))))),
      fun r hr => ?_⟩
    rw [k8.v r hr, k7.v r fun j hj => (hr j hj).2.1, v06 r fun j hj => ⟨(hr j hj).2.2, (hr j hj).2.1⟩]

end VG.Proof.Poly1305.AArch64.Vector
