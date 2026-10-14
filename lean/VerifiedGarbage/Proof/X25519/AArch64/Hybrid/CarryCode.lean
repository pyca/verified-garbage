module

public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Products
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# X25519 on AArch64: the carries of `Neon.prod2`

Untrusted: everything here is checked by Lean. With the limb masks in `v0` and
`v1`, `Neon.carry i` carries coefficient `i` (lanes of `v_{19+i}`) into the
next, as `carryStep i` does with numbers, as long as no lane overflows; the
carries of `Neon.carryOrder` do as `carries`, from bounds that `carriesB`
checks (`carries_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64
open VG.Impl.X25519.AArch64.Neon
open VG.Proof.Ed25519.AArch64 (Scr off word Outside ofs)
open VG.Proof.Curve448.AArch64.Neon (lane_ushr lane_shl)

/-- The carries' masks: `2²⁶ - 1` and `2²⁵ - 1` in the 64-bit lanes of `v0` and `v1`. -/
def CMasks (s : State) : Prop :=
  (∀ e < 2, (vdword (s.v (V 0)) e).toNat = 2 ^ 26 - 1) ∧ ∀ e < 2, (vdword (s.v (V 1)) e).toNat = 2 ^ 25 - 1

/-- Lane `e` of coefficient `k` is `H e k`. -/
def CoefIn (s : State) (H : Nat → Nat → Nat) : Prop :=
  ∀ k < 10, ∀ e < 2, (vdword (s.v (V (19 + k))) e).toNat = H e k

/-- A carry out of `i < 9`, of width `w` with its mask in `v_m`. -/
theorem carry_lt9 {s : State} {H : Nat → Nat → Nat} (hh : CoefIn s H) {i w m : Nat} (hi : i < 9)
    (hw : width i = w) (hmi : maskOf 0 1 i = m) (hm2 : m < 2)
    (hmk : ∀ e < 2, (vdword (s.v (V m)) e).toNat = 2 ^ w - 1)
    (hf : ∀ e < 2, H e (i + 1) + H e i / 2 ^ w < 2 ^ 64) (hw64 : w < 64) (hw0 : 0 < w) :
    WP isa (.block (carry i)) s fun t =>
      CoefIn t (fun e => carryStep i (H e)) ∧ (∀ r, r ≠ V 2 → r ≠ V (19 + i) → r ≠ V (19 + (i + 1)) → t.v r = s.v r) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags := by
  have hn : (i + 1) % 10 = i + 1 := Nat.mod_eq_of_lt (by omega)
  have hc : carry i = [vo (.shift .ushr .d2 (V 2) (V (19 + i)) w), vo (.logic .and (V (19 + i)) (V (19 + i)) (V m)),
      vo (.add .d2 (V (19 + (i + 1))) (V (19 + (i + 1))) (V 2))] := by
    simp only [carry, hw, hmi, hn, show i ≠ 9 by omega, ↓reduceIte, List.nil_append, List.cons_append]
  rw [hc]
  have ok : VShiftOp.ushr.ok VArr.d2.esize w = true := by
    simp only [VShiftOp.ok, VArr.esize, Bool.and_eq_true, decide_eq_true_eq]; omega
  have e1 : VOp.eval s (.shift .ushr .d2 (V 2) (V (19 + i)) w) =
      some (V 2, VArr.d2.map2 (fun w' x y => VShiftOp.eval .ushr w w' x y) (s.v (V 2)) (s.v (V (19 + i)))) := by
    simp only [VOp.eval, ok, ↓reduceIte]
  have n2h : V (19 + i) ≠ V 2 := V_ne _ (by omega) _ (by decide) (by omega)
  have n2n : V (19 + (i + 1)) ≠ V 2 := V_ne _ (by omega) _ (by decide) (by omega)
  have nhn : V (19 + (i + 1)) ≠ V (19 + i) := V_ne _ (by omega) _ (by omega) (by omega)
  have nm2 : V m ≠ V 2 := V_ne _ (by omega) _ (by decide) (by omega)
  have n2h' := n2h.symm
  have n2n' := n2n.symm
  have nhn' := nhn.symm
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of e1, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV,
    and_true]
  refine ⟨fun k hk e he => ?_, fun r r1 r2 r3 => ?_⟩
  · have nmh : V m ≠ V (19 + i) := V_ne _ (by omega) _ (by omega) (by omega)
    simp (disch := assumption) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne]
    by_cases h1 : k = i + 1
    · subst h1
      simp only [RegUpd.v_setV_self]
      rw [lane_addN _ _ he, hh (i + 1) (by omega) e he, lane_ushr _ _ _ he, hh i (by omega) e he]
      simp only [carryStep, carryMul, show i + 1 ≠ i by omega, hn, hw, show i ≠ 9 by omega, ↓reduceIte, Nat.one_mul]
      exact Nat.mod_eq_of_lt (hf e he)
    · have n1 : V (19 + k) ≠ V (19 + (i + 1)) := V_ne _ (by omega) _ (by omega) (by omega)
      rw [RegUpd.v_setV_of_ne _ _ n1]
      by_cases h0 : k = i
      · subst h0
        simp only [RegUpd.v_setV_self]
        rw [lane_and' _ _ hmk he, hh k (by omega) e he]
        simp only [carryStep, hw, ↓reduceIte]
      · have n0 : V (19 + k) ≠ V (19 + i) := V_ne _ (by omega) _ (by omega) (by omega)
        have n2 : V (19 + k) ≠ V 2 := V_ne _ (by omega) _ (by decide) (by omega)
        rw [RegUpd.v_setV_of_ne _ _ n0, RegUpd.v_setV_of_ne _ _ n2, hh k hk e he]
        simp only [carryStep, h0, hn, h1, ↓reduceIte]
  · rw [RegUpd.v_setV_of_ne _ _ r3, RegUpd.v_setV_of_ne _ _ r2, RegUpd.v_setV_of_ne _ _ r1]

theorem carry_9 {s : State} {H : Nat → Nat → Nat} (hh : CoefIn s H)
    (hmk : ∀ e < 2, (vdword (s.v (V 1)) e).toNat = 2 ^ 25 - 1)
    (hf : ∀ e < 2, H e 0 + 19 * (H e 9 / 2 ^ 25) < 2 ^ 64 ∧ 19 * (H e 9 / 2 ^ 25) < 2 ^ 64) :
    WP isa (.block (carry 9)) s fun t =>
      CoefIn t (fun e => carryStep 9 (H e)) ∧ (∀ r, r ≠ V 2 → r ≠ V 3 → r ≠ V 28 → r ≠ V 19 → t.v r = s.v r) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags := by
  simp only [carry, width, maskOf, Nat.reduceMod, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff, List.nil_append,
    List.cons_append]
  repeat refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV,
    and_true]
  refine ⟨fun k hk e he => ?_, fun r r1 r2 r3 r4 => ?_⟩
  · simp (disch := decide) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne]
    have t := hf e he
    by_cases h0 : k = 0
    · subst h0
      simp only [Nat.add_zero, RegUpd.v_setV_self]
      rw [lane_addN _ _ he, lane_addN _ _ he, lane_addN _ _ he, lane_addN _ _ he, lane_shl _ _ _ he,
        lane_ushr _ _ _ he, hh 0 (by decide) e he, hh 9 (by decide) e he]
      simp only [carryStep, carryMul, width, Nat.reduceMod, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff]
      generalize H e 9 / 2 ^ 25 = c at t ⊢
      omega
    · have n0 : V (19 + k) ≠ V 19 := V_ne _ (by omega) _ (by decide) (by omega)
      rw [RegUpd.v_setV_of_ne _ _ n0]
      by_cases h9 : k = 9
      · subst h9
        simp only [Nat.reduceAdd]
        simp (disch := decide) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne]
        rw [lane_and' _ _ hmk he, hh 9 (by decide) e he]
        simp only [carryStep, width, Nat.reduceMod, ↓reduceIte, Nat.reduceEqDiff]
      · have n9 : V (19 + k) ≠ V 28 := V_ne _ (by omega) _ (by decide) (by omega)
        have n2 : V (19 + k) ≠ V 2 := V_ne _ (by omega) _ (by decide) (by omega)
        have n3 : V (19 + k) ≠ V 3 := V_ne _ (by omega) _ (by decide) (by omega)
        simp (disch := assumption) only [RegUpd.v_setV_of_ne]
        rw [hh k hk e he]
        simp only [carryStep, h0, h9, ↓reduceIte, Nat.reduceAdd, Nat.reduceMod]
  · simp (disch := assumption) only [RegUpd.v_setV_of_ne]

theorem carry_ok {s : State} {H : Nat → Nat → Nat} (hm : CMasks s) (hh : CoefIn s H) {i : Nat} (hi : i < 10)
    (hf : ∀ e < 2, H e ((i + 1) % 10) + carryMul i * (H e i / 2 ^ width i) < 2 ^ 64 ∧
      19 * (H e i / 2 ^ width i) < 2 ^ 64) :
    WP isa (.block (carry i)) s fun t =>
      CoefIn t (fun e => carryStep i (H e)) ∧ CMasks t ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags := by
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · have hn : (i + 1) % 10 = i + 1 := Nat.mod_eq_of_lt (by omega)
    have hf' : ∀ e < 2, H e (i + 1) + H e i / 2 ^ width i < 2 ^ 64 := fun e he => by
      have := (hf e he).1
      simp only [hn, carryMul, show i ≠ 9 by omega, ↓reduceIte, Nat.one_mul] at this
      exact this
    have post : ∀ t : State, CoefIn t (fun e => carryStep i (H e)) →
        (∀ r, r ≠ V 2 → r ≠ V (19 + i) → r ≠ V (19 + (i + 1)) → t.v r = s.v r) → CMasks t := fun t _ tv =>
      ⟨fun e he => by
        rw [tv _ (by decide) (V_ne _ (by decide) _ (by omega) (by omega)) (V_ne _ (by decide) _ (by omega) (by omega))]
        exact hm.1 e he,
       fun e he => by
        rw [tv _ (by decide) (V_ne _ (by decide) _ (by omega) (by omega)) (V_ne _ (by decide) _ (by omega) (by omega))]
        exact hm.2 e he⟩
    by_cases hp : i % 2 = 0
    · have hw : width i = 26 := by simp [width, hp]
      refine WP.mono (carry_lt9 hh h9 hw (by simp [maskOf, hp]) (by decide) hm.1 (fun e he => hw ▸ hf' e he)
        (by decide) (by decide)) fun t ⟨tc, tv, rest⟩ => ⟨tc, post t tc tv, rest⟩
    · have hw : width i = 25 := by simp [width, hp]
      refine WP.mono (carry_lt9 hh h9 hw (by simp [maskOf, hp]) (by decide) hm.2 (fun e he => hw ▸ hf' e he)
        (by decide) (by decide)) fun t ⟨tc, tv, rest⟩ => ⟨tc, post t tc tv, rest⟩
  · have h : i = 9 := by omega
    subst h
    refine WP.mono (carry_9 hh hm.2 fun e he => ?_) fun t ⟨tc, tv, rest⟩ => ⟨tc, ⟨fun e he => ?_, fun e he => ?_⟩, rest⟩
    · have := hf e he
      simp only [carryMul, width, Nat.reduceAdd, Nat.reduceMod, ↓reduceIte, Nat.reduceEqDiff] at this
      exact this
    · rw [tv _ (by decide) (by decide) (by decide) (by decide)]; exact hm.1 e he
    · rw [tv _ (by decide) (by decide) (by decide) (by decide)]; exact hm.2 e he

theorem carries_go {s : State} : ∀ (l : List Nat) (H : Nat → Nat → Nat) (B : Nat → Nat), (∀ i ∈ l, i < 10) →
    CMasks s → CoefIn s H → (∀ e < 2, ∀ k < 10, H e k ≤ B k) → (carriesB B l).2 = true →
    WP isa (.block (l.flatMap carry)) s fun t =>
      CoefIn t (fun e => l.foldl (fun h i => carryStep i h) (H e)) ∧
      (∀ e < 2, ∀ k < 10, l.foldl (fun h i => carryStep i h) (H e) k ≤ (carriesB B l).1 k) ∧
      CMasks t ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags
  | [], H, B, _, hm, hh, hb, _ => WP.block_nil ⟨hh, hb, hm, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | i :: l, H, B, hl, hm, hh, hb, hfit => by
    simp only [carriesB, Bool.and_eq_true] at hfit
    obtain ⟨hfi, hfl⟩ := hfit
    simp only [carryFits, Bool.and_eq_true, decide_eq_true_eq] at hfi
    have hi := hl i List.mem_cons_self
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (carry_ok hm hh hi fun e he => ⟨?_, ?_⟩) fun t ⟨tc, tm, tmm, tg, tr, tw, tsp, tf⟩ =>
      WP.mono (carries_go l _ _ (fun j hj => hl j (List.mem_cons_of_mem _ hj)) tm tc
        (fun e he k hk => carryStep_le (fun k hk => hb e he k hk) hi k hk) hfl)
        fun u ⟨uc, ub, um, umm, ug, ur, uw, usp, uf⟩ =>
          ⟨uc, ub, um, umm.trans tmm, ug.trans tg, ur.trans tr, uw.trans tw, usp.trans tsp, uf.trans tf⟩
    · have h1 := carryStep_le (fun k hk => hb e he k hk) hi ((i + 1) % 10) (Nat.mod_lt _ (by decide))
      have h2 : carryStep i (H e) ((i + 1) % 10) = H e ((i + 1) % 10) + carryMul i * (H e i / 2 ^ width i) := by
        simp only [carryStep, show (i + 1) % 10 ≠ i by omega, ↓reduceIte]
      omega
    · have := Nat.mul_le_mul_left 19 (Nat.div_le_div_right (c := 2 ^ width i) (hb e he i hi))
      omega

/-- `prod2`'s carries, from the products' coefficients: `carries`, below 2²⁷. -/
theorem carries_ok {s : State} {base : Addr} (hs : Scratch s base) (hc : Consts s.mem base) {H : Nat → Nat → Nat}
    (hh : CoefIn s H) (hb : ∀ e < 2, ∀ k < 10, H e k ≤ prodB k) :
    WP isa (.block VG.Impl.X25519.AArch64.Neon.carries) s fun t =>
      CoefIn t (fun e => Hybrid.carries (H e)) ∧ (∀ e < 2, ∀ k < 10, Hybrid.carries (H e) k < 2 ^ 27) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags := by
  rw [VG.Impl.X25519.AArch64.Neon.carries, WP.block_append_iff]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs 0 (by decide) (by decide), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scratch_setV hs _ _) 1 (by decide) (by decide), ?_⟩
  refine WP.block_nil_iff.mpr ?_
  have hm : CMasks ((s.setV (V 0) (s.mem.read (off base M26) 16)).setV (V 1)
      ((s.setV (V 0) (s.mem.read (off base M26) 16)).mem.read (off base M25) 16)) :=
    ⟨fun e he => by
      simp (disch := decide) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne]
      rw [vdword_ld _ _ _ he]; exact hc.1 e he,
     fun e he => by
      simp only [RegUpd.v_setV_self, RegUpd.mem_setV]
      rw [vdword_ld _ _ _ he]; exact hc.2.1 e he⟩
  have hh' : CoefIn ((s.setV (V 0) (s.mem.read (off base M26) 16)).setV (V 1)
      ((s.setV (V 0) (s.mem.read (off base M26) 16)).mem.read (off base M25) 16)) H := fun k hk e he => by
    rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by decide) (by omega)),
      RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by decide) (by omega))]
    exact hh k hk e he
  refine WP.mono (carries_go _ H prodB (by decide) hm hh' hb carriesB_prodB.1)
    fun t ⟨tc, tb, _, tm, tg, tr, tw, tsp, tf⟩ =>
      ⟨tc, fun e he k hk => Nat.lt_of_le_of_lt (tb e he k hk) (carriesB_prodB.2 k hk), tm, tg, tr, tw, tsp, tf⟩

end VG.Proof.X25519.AArch64.Hybrid
