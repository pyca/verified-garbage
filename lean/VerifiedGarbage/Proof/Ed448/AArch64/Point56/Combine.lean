import VerifiedGarbage.Proof.X448.AArch64.Base.Step
import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
import VerifiedGarbage.Proof.Curve448.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave

/-!
# Ed448's comb on AArch64: `16 A + B` by calls

Untrusted: everything here is checked by Lean. `combineCall` (the comb's
`A := 16 A + B` by calls of `vg_ed448_r56_point_add`) leaves what X448's
`Base.combine` does (`combineCall_ok`, as `combine_ok`): `B` kept in slots 0–2,
`A` moved to slots 3–5 and added to a copy of itself in slots 6–8 four times
(`addCall_ok`, whose addition is `addPt` with 0 in slot 19), `B` added, and the
sum moved to slots 0–2; the return address kept in a lane of `v8` across the
calls (`WP.preservedV`).
-/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64 VG.Impl.Ed448.AArch64.Point56
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genPt genPt_eq temps zero_env StepInv)
open VG.Proof.Ed448 (Rep baseAff)
open VG.Proof.X448 (addPt addPt_rep)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

/-- What `combineMid` keeps: `Frame` but for the return address. -/
structure MFrame (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem

theorem MFrame.keeps {s₀ s t : State} {base : Addr} {rs : List Reg} (h : MFrame s₀ base s) (k : Keeps rs s t)
    (h312 : .x3 ∉ rs ∧ .x12 ∉ rs) (h20 : .x20 ∉ rs) (hm : t.mem = s.mem) : MFrame s₀ base t :=
  ⟨h.scr.of_keeps k h312, by rw [hm]; exact h.env, by rw [hm]; exact h.zero,
    by rw [k.1 _ h20]; exact h.out, by rw [k.2.1]; exact h.rd, by rw [k.2.2]; exact h.wr,
    by rw [hm]; exact h.mem⟩

theorem FV_of_limbs {m m' : Mem} {base : Addr} {o o' : Nat} (h : ∀ i < 8, limbs m' base o' i = limbs m base o i) :
    FV m' base o' = FV m base o := congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr h)

/-- Three slots copied from three others: the copies' limbs, and every other slot's kept. -/
theorem copy3_ok {s₀ s : State} {base : Addr} (h : MFrame s₀ base s) (o a : Nat) (ho : o + 3 ≤ 10) (ha : a + 3 ≤ 10)
    (hsep : o + 3 ≤ a ∨ a + 3 ≤ o) :
    WP isa (.block (copy3 o a)) s fun t => MFrame s₀ base t ∧
      pt (EV t.mem base) ⟨o, by omega⟩ ⟨o + 1, by omega⟩ ⟨o + 2, by omega⟩ =
        pt (EV s.mem base) ⟨a, by omega⟩ ⟨a + 1, by omega⟩ ⟨a + 2, by omega⟩ ∧
      (∀ i : Index, (i.val < o ∨ o + 3 ≤ i.val) → ∀ j < 8, limbs t.mem base (slot i.val) j =
        limbs s.mem base (slot i.val) j) ∧
      Keeps VG.Proof.X448.AArch64.clob s t := by
  have hs := h.scr
  rw [copy3, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (o := slot o) (a := slot a) (by simp only [slot]; omega)
    (by simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot]; omega)
    (Or.inr (by simp only [slot]; omega))) fun t1 ⟨v1, o1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs1 (o := slot (o + 1)) (a := slot (a + 1))
    (by simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot]; omega)
    (by simp only [slot]; omega) (Or.inr (by simp only [slot]; omega))) fun t2 ⟨v2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs2 (o := slot (o + 2)) (a := slot (a + 2))
    (by simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot]; omega)
    (by simp only [slot]; omega) (Or.inr (by simp only [slot]; omega))) fun t ⟨v3, o3, k3⟩ => ?_
  have hc : ∀ c < 3, ∀ j < 8, limbs t.mem base (slot (o + c)) j = limbs s.mem base (slot (a + c)) j := by
    intro c hc j hj
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
    · rw [o3.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
        o2.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega), Nat.add_zero, v1 j hj,
        Nat.add_zero]
    · rw [o3.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega), v2 j hj,
        o1.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)]
    · rw [v3 j hj, o2.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
        o1.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)]
  have hk : ∀ i : Index, (i.val < o ∨ o + 3 ≤ i.val) → ∀ j < 8, limbs t.mem base (slot i.val) j =
      limbs s.mem base (slot i.val) j := fun i hi j hj => by
    have := i.isLt
    rw [o3.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o2.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o1.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)]
  have k : Keeps VG.Proof.X448.AArch64.clob s t := (k1.trans k2).trans k3
  have om : Outside base (slot o) 384 s.mem t.mem := by
    intro x hx
    rw [o3 x (by simp only [slot] at hx ⊢; omega), o2 x (by simp only [slot] at hx ⊢; omega),
      o1 x (by simp only [slot] at hx ⊢; omega)]
  refine ⟨⟨hs.of_keeps k (by decide), fun i => ?_, fun w hw => ?_, by rw [k.1 _ (by decide)]; exact h.out,
    by rw [k.2.1]; exact h.rd, by rw [k.2.2]; exact h.wr, h.mem.trans fun x h1 _ => om x (by
      simp only [slot] at h1 ⊢; omega)⟩, ?_, hk, k⟩
  · by_cases hi : i.val < o ∨ o + 3 ≤ i.val
    · exact fun j hj => by rw [hk i hi j hj]; exact h.env i j hj
    · have e : i.val = o + (i.val - o) := by omega
      exact fun j hj => by
        show limbs t.mem base (slot i.val) j < Ib
        rw [e, hc _ (by omega) j hj]; exact h.env ⟨a + (i.val - o), by omega⟩ j hj
  · rw [hk 19 (by simp; omega) w hw]; exact h.zero w hw
  · simp only [pt, VG.Proof.X448.AArch64.Weak.E]
    rw [FV_of_limbs (o := slot a) (o' := slot o) (fun j hj => by simpa using hc 0 (by decide) j hj),
      FV_of_limbs (hc 1 (by decide)), FV_of_limbs (hc 2 (by decide))]

/-- The point in slots 3–5 added to the point in slots 6–8, by a call. -/
theorem addC_ok {s₀ s : State} {base : Addr} (h : MFrame s₀ base s) :
    WP isa addCall s fun t => MFrame s₀ base t ∧ Keeps (.x30 :: VG.Proof.X448.AArch64.Fast.fclob) s t ∧
      pt (EV t.mem base) 3 4 5 = addPt (pt (EV s.mem base) 3 4 5) (pt (EV s.mem base) 6 7 8) ∧
      (∀ i : Index, i.val < 3 → EV t.mem base i = EV s.mem base i) := by
  refine WP.mono (addCall_ok h.scr h.env (zero_env h.zero).2) fun t ⟨k, b, sm, _, _, _, e, _⟩ => ?_
  have n19 : (19 : Index) ∉ temps ++ [3, 4, 5] := by decide
  have nt : ∀ i : Index, i.val < 3 → i ∉ temps ++ [3, 4, 5] := by decide
  refine ⟨⟨k.scr h.scr, b, fun w hw => by rw [sm 19 n19 w hw]; exact h.zero w hw,
    by rw [k.regs.1 _ (by decide)]; exact h.out, by rw [k.regs.2.1]; exact h.rd, by rw [k.regs.2.2]; exact h.wr,
    h.mem.trans k.mem⟩, k.regs, ?_, fun i hi => Same.env sm (nt i hi)⟩
  rw [e, genEnv_pt, (zero_env h.zero).1, genPt_eq]

theorem setX1_ok (s : State) :
    WP isa (.block [.movz .w .x1 4 0]) s fun t => t.gpr .x1 = BitVec.ofNat 64 4 ∧ Keeps [.x1] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl⟩, rfl⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

private theorem dec_x1 : ∀ n < 4, BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 n ∧
    (BitVec.ofNat 64 n != 0) = decide (n ≠ 0) := by decide

theorem decX1_ok (s : State) {n : Nat} (hn : n < 4) (hc : s.gpr .x1 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x1 .x1 1]) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 n ∧ Keeps [.x1] s t ∧ t.mem = s.mem ∧
        (t.gpr .x1 != 0) = decide (n ≠ 0) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (1 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc,
    (dec_x1 n hn).1, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl,
    (dec_x1 n hn).2⟩

/-- The doublings' state with `m` of them left: `A` in slots 3–5, `B` in 0–2. -/
structure DInv (s₀ : State) (base : Addr) (v w : ℤ) (m : Nat) (s : State) : Prop where
  frame : MFrame s₀ base s
  counter : s.gpr .x1 = BitVec.ofNat 64 m
  a : Rep (pt (EV s.mem base) 3 4 5) ((2 ^ (4 - m) * v) • baseAff)
  b : Rep (pt (EV s.mem base) 0 1 2) (w • baseAff)

theorem dbl_ok {s₀ s : State} {base : Addr} {v w : ℤ} {m : Nat} (hm : 1 ≤ m) (hm4 : m ≤ 4)
    (h : DInv s₀ base v w m s) :
    WP isa (.seq (.block (copy3 6 3)) (.seq addCall (.block [.subImm .x .x1 .x1 1]))) s
      fun t => DInv s₀ base v w (m - 1) t ∧ (t.gpr .x1 != 0) = decide (m - 1 ≠ 0) := by
  refine WP.seq (WP.mono (copy3_ok h.frame 6 3 (by decide) (by decide) (by decide))
    fun t1 ⟨f1, p1, k1, g1⟩ => ?_)
  have e1 : ∀ i : Index, i.val < 6 → EV t1.mem base i = EV s.mem base i := fun i hi =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (k1 i (.inl hi)))
  refine WP.seq (WP.mono (addC_ok f1) fun t2 ⟨f2, kk2, q2, b2⟩ => ?_)
  refine WP.mono (decX1_ok (n := m - 1) t2 (by omega) (by
      rw [kk2.1 _ (by decide), g1.1 _ (by decide), h.counter]; congr 1; omega))
    fun u ⟨uc, uk, um, uz⟩ => ⟨⟨f2.keeps uk (by decide) (by decide) um, uc, ?_, ?_⟩, uz⟩
  · rw [um, q2]
    have p3 : pt (EV t1.mem base) 3 4 5 = pt (EV s.mem base) 3 4 5 := by
      simp only [pt]; rw [e1 3 (by decide), e1 4 (by decide), e1 5 (by decide)]
    have p6 : pt (EV t1.mem base) 6 7 8 = pt (EV s.mem base) 3 4 5 := p1
    rw [p3, p6]
    have := addPt_rep h.a h.a
    rw [← add_smul] at this
    rw [show (2 : ℤ) ^ (4 - (m - 1)) * v = 2 ^ (4 - m) * v + 2 ^ (4 - m) * v by
      rw [show 4 - (m - 1) = (4 - m) + 1 by omega, pow_succ]; ring]
    exact this
  · rw [um]
    simp only [pt]
    rw [b2 0 (by decide), b2 1 (by decide), b2 2 (by decide), e1 0 (by decide), e1 1 (by decide),
      e1 2 (by decide)]
    exact h.b

theorem EV_of_keep {m m' : Mem} {base : Addr} {i : Index}
    (h : ∀ j < 8, limbs m' base (slot i.val) j = limbs m base (slot i.val) j) : EV m' base i = EV m base i :=
  congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr h)

/-- `combineMid`: `16 A + B` in slots 0–2, for `A` in slots 0–2 and `B` in 3–5. -/
theorem combineMid_ok {s₀ s : State} {base : Addr} {v w : ℤ} (f0 : MFrame s₀ base s)
    (ha : Rep (pt (EV s.mem base) 0 1 2) (v • baseAff)) (hb : Rep (pt (EV s.mem base) 3 4 5) (w • baseAff)) :
    WP isa combineMid s fun t => MFrame s₀ base t ∧
      Rep (pt (EV t.mem base) 0 1 2) ((16 * v + w) • baseAff) := by
  unfold combineMid
  rw [WP.seq_iff, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy3_ok f0 6 0 (by decide) (by decide) (by decide)) fun t1 ⟨f1, p1, k1, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy3_ok f1 0 3 (by decide) (by decide) (by decide)) fun t2 ⟨f2, p2, k2, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy3_ok f2 3 6 (by decide) (by decide) (by decide)) fun t3 ⟨f3, p3, k3, _⟩ => ?_
  refine WP.mono (setX1_ok t3) fun t4 ⟨c4, kk4, m4⟩ => ?_
  have p1' : pt (EV t1.mem base) 6 7 8 = pt (EV s.mem base) 0 1 2 := p1
  have p2' : pt (EV t2.mem base) 0 1 2 = pt (EV t1.mem base) 3 4 5 := p2
  have p3' : pt (EV t3.mem base) 3 4 5 = pt (EV t2.mem base) 6 7 8 := p3
  have pA : pt (EV t3.mem base) 3 4 5 = pt (EV s.mem base) 0 1 2 := by
    have q : pt (EV t2.mem base) 6 7 8 = pt (EV t1.mem base) 6 7 8 := by
      simp only [pt]
      rw [EV_of_keep (k2 6 (.inr (by decide))), EV_of_keep (k2 7 (.inr (by decide))),
        EV_of_keep (k2 8 (.inr (by decide)))]
    rw [p3', q, p1']
  have pB : pt (EV t3.mem base) 0 1 2 = pt (EV s.mem base) 3 4 5 := by
    have q : pt (EV t3.mem base) 0 1 2 = pt (EV t2.mem base) 0 1 2 := by
      simp only [pt]
      rw [EV_of_keep (k3 0 (.inl (by decide))), EV_of_keep (k3 1 (.inl (by decide))),
        EV_of_keep (k3 2 (.inl (by decide)))]
    have q' : pt (EV t1.mem base) 3 4 5 = pt (EV s.mem base) 3 4 5 := by
      simp only [pt]
      rw [EV_of_keep (k1 3 (.inl (by decide))), EV_of_keep (k1 4 (.inl (by decide))),
        EV_of_keep (k1 5 (.inl (by decide)))]
    rw [q, p2', q']
  have d4 : DInv s₀ base v w 4 t4 :=
    ⟨f3.keeps kk4 (by decide) (by decide) m4, c4, by rw [m4, pA]; simpa using ha, by rw [m4, pB]; exact hb⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun t => DInv s₀ base v w 0 t)
    (fun m (t : State) => 1 ≤ m ∧ m ≤ 4 ∧ DInv s₀ base v w m t) ?_ 4 t4 ⟨by decide, le_refl _, d4⟩) ?_)
  · intro m t ⟨h1, h4, ht⟩
    refine WP.mono (dbl_ok h1 h4 ht) fun u ⟨hu, hz⟩ => ?_
    simp only [eval, State.read, BitVec.setWidth_eq, hz]
    by_cases hm : m = 1
    · subst hm; exact .inl ⟨rfl, hu⟩
    · exact .inr ⟨by simp only [decide_eq_true (by omega : m - 1 ≠ 0)], m - 1,
        by omega, by omega, by omega, hu⟩
  · intro t ht
    refine WP.seq (WP.mono (copy3_ok ht.frame 6 0 (by decide) (by decide) (by decide))
      fun t5 ⟨f5, p5, k5, _⟩ => ?_)
    refine WP.seq (WP.mono (addC_ok f5) fun t6 ⟨f6, _, q6, _⟩ => ?_)
    refine WP.mono (copy3_ok f6 0 3 (by decide) (by decide) (by decide)) fun t7 ⟨f7, p7, _, _⟩ => ⟨f7, ?_⟩
    have p5' : pt (EV t5.mem base) 6 7 8 = pt (EV t.mem base) 0 1 2 := p5
    have p7' : pt (EV t7.mem base) 0 1 2 = pt (EV t6.mem base) 3 4 5 := p7
    have a5 : pt (EV t5.mem base) 3 4 5 = pt (EV t.mem base) 3 4 5 := by
      simp only [pt]
      rw [EV_of_keep (k5 3 (.inl (by decide))), EV_of_keep (k5 4 (.inl (by decide))),
        EV_of_keep (k5 5 (.inl (by decide)))]
    rw [p7', q6, a5, p5']
    have r := addPt_rep ht.a ht.b
    rw [← add_smul, show (2 : ℤ) ^ (4 - 0) * v + w = 16 * v + w by norm_num] at r
    exact r

/-- **`16 A + B` by calls**, from `Frame`: `[16 v + w] B` in `A`, the return address kept. -/
theorem combineCall_frame {s₀ s : State} {base : Addr} {v w : ℤ} (h : VG.Proof.X448.AArch64.Base.Frame s₀ base s)
    (ha : Rep (pt (EV s.mem base) 0 1 2) (v • baseAff)) (hb : Rep (pt (EV s.mem base) 3 4 5) (w • baseAff)) :
    WP isa combineCall s fun t => VG.Proof.X448.AArch64.Base.Frame s₀ base t ∧
      Rep (pt (EV t.mem base) 0 1 2) ((16 * v + w) • baseAff) := by
  unfold combineCall
  rw [WP.seq_iff]
  refine WP.mono (insOf_ok [(.x30, .v8, 0)] s (by decide) (by decide)) fun t₁ ⟨g₁, m₁, r₁, w₁, _, l₁, _⟩ => ?_
  have f₁ : MFrame s₀ base t₁ :=
    ⟨h.scr.of_keeps (rs := []) ⟨fun r _ => by rw [g₁], r₁, w₁⟩ (by decide), m₁ ▸ h.env, m₁ ▸ h.zero,
      by rw [g₁]; exact h.out, by rw [r₁]; exact h.rd, by rw [w₁]; exact h.wr, m₁ ▸ h.mem⟩
  rw [WP.seq_iff]
  refine WP.mono (WP.preservedV (combineMid_ok f₁ (m₁ ▸ ha) (m₁ ▸ hb)) (by lit_decide))
    fun t₂ ⟨⟨f₂, r₂⟩, v₂⟩ => ?_
  refine WP.mono (umovOf_ok [(.x30, .v8, 0)] t₂ (by decide) (by decide)) fun u ⟨um, ur, uw, _, ul, uo⟩ => ?_
  have l30 : u.gpr .x30 = s₀.gpr .x30 := by
    rw [ul _ List.mem_cons_self]
    show (t₂.v .v8).extractLsb' (64 * 0) 64 = _
    rw [v₂ .v8 (by decide)]
    exact (l₁ _ List.mem_cons_self).trans h.lr
  have ku : Keeps [.x30] t₂ u := ⟨fun r hr => uo r (by simpa using hr), ur, uw⟩
  refine ⟨⟨f₂.scr.of_keeps ku (by decide), um ▸ f₂.env, um ▸ f₂.zero, l30,
    by rw [ku.1 _ (by decide)]; exact f₂.out, by rw [ur]; exact f₂.rd, by rw [uw]; exact f₂.wr, um ▸ f₂.mem⟩, ?_⟩
  rw [um]
  exact r₂

/-- **`16 A + B` by calls**, as `combine_ok`: `[k] B` in `A`, the return address kept. -/
theorem combineCall_ok {n : Nat} {s₀ s : State} {base : Addr} {k : Nat} (hk : k < 256 ^ n)
    (h : StepInv n s₀ base k n s) :
    WP isa combineCall s fun t => VG.Proof.X448.AArch64.Base.Frame s₀ base t ∧ Rep (pt (EV t.mem base) 0 1 2) ((k : ℤ) • baseAff) :=
  WP.mono (combineCall_frame h.frame h.odd h.even) fun t ⟨f, r⟩ => ⟨f, by rw [← VG.Proof.X448.comb_total hk]; exact r⟩

end VG.Proof.Ed448.AArch64.Point56
