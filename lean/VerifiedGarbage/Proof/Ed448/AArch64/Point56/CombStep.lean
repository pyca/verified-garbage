import VerifiedGarbage.Proof.Ed448.AArch64.Point56.CombCall
import VerifiedGarbage.Proof.X448.AArch64.Base.Loop

/-!
# Ed448's comb on AArch64: the steps, calling the additions

Untrusted: everything here is checked by Lean. `combStep` is X448's comb step
(`Base.stepN`) with both entries negated first and added by one call of
`vg_ed448_r56_comb_add` (`combAddCall_ok`): it takes the invariant from `j` to
`j + 1` as `step_ok` does, but for the return address, which the call
overwrites and the loop keeps in a lane of `v8` (`StepInvC`). `combLoop_ok`:
the loop, between that lane's save and restore, as `loop_ok`.
-/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base VG.Impl.Ed448.AArch64.Point56
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (nib mag addPt addPt_rep basePt negAff baseEntry_ok nib_lt mag_lt combG oddSumZ evenSumZ)
open VG.Proof.X448.AArch64.Base (StepInv Bits TblAt Masks Selected digits_ok select_ok selected_env negate_ok
  next_ok entrySlots entry_eq acc_step affEnv affPt_eq pt temps zero_env)
open VG.Proof.Ed448 (Rep baseAff)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `StepInv` but for the return address, kept in the low half of `v8`. -/
structure StepInvC (n : Nat) (s₀ : State) (base : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ n
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  bits : Bits n base k s.mem
  odd : Rep (pt (EV s.mem base) 0 1 2) (((combG n : ℤ) + oddSumZ k j) • baseAff)
  even : Rep (pt (EV s.mem base) 3 4 5) (((combG n : ℤ) + evenSumZ k j) • baseAff)
  lane : (s.v .v8).extractLsb' 0 64 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem
  tbl : TblAt s base (s₀.syms combSym)

theorem combStep_eq (n : Nat) : combStep n =
    .seq (.block digits) (.seq (.block select) (.seq (.block (
      negate (slot (6 : Index).val) (BITS + 4) (slot (10 : Index).val) ++
      negate (slot (8 : Index).val) BITS (slot (10 : Index).val))) (.seq combAddCall
      (.block ([.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 n] : List Instr))))) := rfl

theorem digits_keepsV : (Code.block digits : Prog isa).allInstrs keepsV = true := by lit_decide
theorem select_keepsV : (Code.block select : Prog isa).allInstrs keepsV = true := by lit_decide
theorem negO_keepsV : (Code.block (negate (slot (6 : Index).val) (BITS + 4) (slot (10 : Index).val)) : Prog isa).allInstrs
    keepsV = true := by lit_decide
theorem negE_keepsV : (Code.block (negate (slot (8 : Index).val) BITS (slot (10 : Index).val)) : Prog isa).allInstrs
    keepsV = true := by lit_decide
theorem next_keepsV (n : Nat) :
    (Code.block ([.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 n] : List Instr) : Prog isa).allInstrs keepsV =
      true := rfl

/-- An addition's environment keeps every slot but its result's and the temporaries. -/
theorem affEnv_keep (x1 y1 z1 x2 y2 : Index) (e : Env) (i : Index)
    (hi : i ∉ [x1, y1, z1, 10, 11, 12, 13, 14, 15, 16, 17, 18]) : affEnv x1 y1 z1 x2 y2 e i = e i := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  obtain ⟨h1, h2, h3, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hi
  simp only [affEnv, VG.Proof.X448.AArch64.opCopy, Function.update_apply, h1, h2, h3, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, ite_false]

theorem bits_of_out2 {base : Addr} {n k : Nat} {s : State} {m m' : Mem} (hn : n ≤ 57) (hs : Scr s base)
    (h : Bits n base k m) (hk : Outside2 base 64 2816 ACC 1152 m m') : Bits n base k m' := fun q hq => by
  have hn := hs.nowrap
  rw [hk _ (by rw [VG.Proof.X448.AArch64.Base.ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [VG.Proof.X448.AArch64.Base.ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
  exact h q hq

theorem combStep_ok {n : Nat} (hn : n ≤ 57) {s₀ s : State} {base : Addr} {k j : Nat}
    (h : StepInvC n s₀ base k j s) (hj : j < n) (hsy : s.syms = s₀.syms) :
    WP isa (combStep n) s fun t =>
      (t.gpr .x9 != 0) = decide (j + 1 ≠ n) ∧ StepInvC n s₀ base k (j + 1) t := by
  obtain ⟨_, hs, hb, hz, hc, hbits, hodd, heven, hlane, hout, hrd, hwr, hmem, htbl⟩ := h
  have no := nib_lt k (2 * j + 1)
  have ne := nib_lt k (2 * j)
  rw [combStep_eq n]
  -- The digits.
  refine WP.seq (WP.mono_syms (WP.preservedV (digits_ok hs hn hj hc hbits) digits_keepsV)
    fun t1 ⟨⟨d1, m1⟩, v1⟩ sy1 => ?_)
  have hs1 : Scr t1 base := hs.of_keeps d1.keeps (by decide)
  have hb1 : BEnv t1.mem base := by rw [m1]; exact hb
  have hm1 : Masks (mag (nib k (2 * j + 1))) (mag (nib k (2 * j))) t1 :=
    ⟨d1.oddMask, d1.evenMask, d1.oddZero, d1.evenZero⟩
  have hc1 : t1.gpr .x19 = BitVec.ofNat 64 j := by rw [d1.keeps.1 _ (by decide)]; exact hc
  -- The selection.
  have tb1 : TblAt t1 base (s₀.syms combSym) :=
    htbl.of_far (by rw [d1.keeps.2.1, d1.keeps.2.2]) fun x _ => by rw [m1]
  refine WP.seq (WP.mono (WP.preservedV (select_ok hs1 tb1 (by rw [sy1, hsy]) (by omega) hc1 (mag_lt no)
    (mag_lt ne) hm1) select_keepsV) fun t2 ⟨h2, v2⟩ => ?_)
  obtain ⟨b2, s2, v6, v7, v8, v9, bnd2⟩ := selected_env hs1 hb1 h2
  have hs2 : Scr t2 base := hs1.of_keeps h2.2.2 (by decide)
  have hc2 : t2.gpr .x19 = BitVec.ofNat 64 j := by rw [h2.2.2.1 _ (by decide)]; exact hc1
  have bits2 : Bits n base k t2.mem := fun q hq => by
    have hn := hs.nowrap
    have ho : VG.Proof.X448.AArch64.ofs base (off base (BITS + q)) = BITS + q :=
      VG.Proof.X448.AArch64.Base.ofs_off0 base (by simp only [BITS]; omega)
    rw [h2.2.1 _ (by rw [ho]; simp only [OX, BITS, slot]; omega), m1]
    exact hbits q hq
  have z2 : ∀ w < 8, limbs t2.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s2 19 (by decide) w hw]; rw [m1]; exact hz w hw
  have e1 : EV t1.mem base = EV s.mem base := by rw [m1]
  -- Both entries, negated for negative digits.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.preservedV (negate_ok hs2 b2 (k := k) (i := 2 * j + 1)
    (o := BITS + 4) 6 (by decide) hn (by omega) (by omega) (by simp only [BITS]; omega)
    (by simp only [BITS]; omega) hc2 bits2 (bnd2 6 (by decide)) (zero_env z2).2) negO_keepsV)
    fun t3 ⟨⟨k3, b3, s3, e3⟩, v3⟩ => ?_
  refine WP.mono (WP.preservedV (negate_ok (k3.scr hs2) b3 (k := k) (j := j) (i := 2 * j) (o := BITS) 8 (by decide) hn
    (by omega) (by omega) (by omega) (by simp only [BITS]; omega) (by rw [k3.regs.1 _ (by decide)]; exact hc2)
    (VG.Proof.X448.AArch64.Base.Bits.of_fkeep hn hs2 bits2 k3) (s3.bnd (by decide) (bnd2 8 (by decide)))
    (s3.bnd (by decide) (zero_env z2).2)) negE_keepsV) fun t5 ⟨⟨k5, b5, s5, e5⟩, v5'⟩ => ?_
  have hs3 := k3.scr hs2
  have hs5 := k5.scr hs3
  have z5 : ∀ w < 8, limbs t5.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s5 19 (by decide) w hw, s3 19 (by decide) w hw]; exact z2 w hw
  have hc5 : t5.gpr .x19 = BitVec.ofNat 64 j := by
    rw [k5.regs.1 .x19 (by decide), k3.regs.1 .x19 (by decide)]; exact hc2
  -- Both added, by a call.
  refine WP.seq (WP.mono (combAddCall_ok hs5 b5 (zero_env z5).2) fun t6 ⟨k6, b6, s6, _, e6, _⟩ => ?_)
  have hs6 := k6.scr hs5
  have hc6 : t6.gpr .x19 = BitVec.ofNat 64 j := by rw [k6.regs.1 .x19 (by decide)]; exact hc5
  -- The counter.
  refine WP.mono (WP.preservedV (next_ok t6 hn hj hc6) (next_keepsV n)) fun t7 ⟨⟨c7, n7, k7, m7⟩, vn7⟩ =>
    ⟨n7, ?_⟩
  have hs7 : Scr t7 base := hs6.of_keeps k7 (by decide)
  have z6 : ∀ w < 8, limbs t6.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s6 19 (by decide) w hw]; exact z5 w hw
  -- Values of the slots along the way.
  have e2s : ∀ i : Index, i ∉ entrySlots → EV t2.mem base i = EV s.mem base i := fun i hi => by
    rw [Same.env s2 hi, e1]
  have z2v : EV t2.mem base 19 = 0 := (zero_env z2).1
  have t3o : ∀ i : Index, i ≠ 6 → i ≠ 10 → EV t3.mem base i = EV t2.mem base i := fun i h6 h10 => by
    rw [e3]; simp only [VG.Proof.X448.AArch64.opSwap, Function.update_apply, h6, h10, ite_false]
  have t36 : EV t3.mem base 6 =
      if decide (nib k (2 * j + 1) < 8) then EV t2.mem base 19 - EV t2.mem base 6 else EV t2.mem base 6 := by
    rw [e3]; simp only [VG.Proof.X448.AArch64.opSwap, Function.update_apply, show (6 : Index) ≠ 10 by decide, ite_false, ite_true]
  have t5o : ∀ i : Index, i ≠ 8 → i ≠ 10 → EV t5.mem base i = EV t3.mem base i := fun i h8 h10 => by
    rw [e5]; simp only [VG.Proof.X448.AArch64.opSwap, Function.update_apply, h8, h10, ite_false]
  have t58 : EV t5.mem base 8 =
      if decide (nib k (2 * j) < 8) then EV t3.mem base 19 - EV t3.mem base 8 else EV t3.mem base 8 := by
    rw [e5]; simp only [VG.Proof.X448.AArch64.opSwap, Function.update_apply, show (8 : Index) ≠ 10 by decide, ite_false, ite_true]
  have t5v : ∀ i : Index, i ≠ 6 → i ≠ 8 → i ≠ 10 → EV t5.mem base i = EV t2.mem base i := fun i h6 h8 h10 => by
    rw [t5o i h8 h10, t3o i h6 h10]
  have t56 : EV t5.mem base 6 = EV t3.mem base 6 := t5o 6 (by decide) (by decide)
  -- The accumulators.
  have pA : pt (EV t6.mem base) 0 1 2 = addPt (pt (EV s.mem base) 0 1 2)
      (basePt (if nib k (2 * j + 1) < 8 then negAff (Impl.X448.baseTable j (mag (nib k (2 * j + 1))))
        else Impl.X448.baseTable j (mag (nib k (2 * j + 1))))) := by
    have kB : pt (affEnv 3 4 5 8 9 (affEnv 0 1 2 6 7 (EV t5.mem base))) 0 1 2 =
        pt (affEnv 0 1 2 6 7 (EV t5.mem base)) 0 1 2 := by
      simp only [pt]
      rw [affEnv_keep _ _ _ _ _ _ 0 (by decide), affEnv_keep _ _ _ _ _ _ 1 (by decide),
        affEnv_keep _ _ _ _ _ _ 2 (by decide)]
    rw [e6, kB, VG.Proof.X448.AArch64.Base.affEnv_A,
      t5v 0 (by decide) (by decide) (by decide), t5v 1 (by decide) (by decide) (by decide),
      t5v 2 (by decide) (by decide) (by decide), t56, t36, t5v 7 (by decide) (by decide) (by decide),
      t5v 19 (by decide) (by decide) (by decide), z2v, v6, v7, e2s 0 (by decide), e2s 1 (by decide),
      e2s 2 (by decide), affPt_eq, entry_eq _ 0 rfl]
    rfl
  have pB : pt (EV t6.mem base) 3 4 5 = addPt (pt (EV s.mem base) 3 4 5)
      (basePt (if nib k (2 * j) < 8 then negAff (Impl.X448.baseTable j (mag (nib k (2 * j))))
        else Impl.X448.baseTable j (mag (nib k (2 * j))))) := by
    rw [e6, VG.Proof.X448.AArch64.Base.affEnv_B,
      affEnv_keep _ _ _ _ _ _ 3 (by decide), affEnv_keep _ _ _ _ _ _ 4 (by decide),
      affEnv_keep _ _ _ _ _ _ 5 (by decide), affEnv_keep _ _ _ _ _ _ 8 (by decide),
      affEnv_keep _ _ _ _ _ _ 9 (by decide), affEnv_keep _ _ _ _ _ _ 19 (by decide),
      t5v 3 (by decide) (by decide) (by decide), t5v 4 (by decide) (by decide) (by decide),
      t5v 5 (by decide) (by decide) (by decide), t58, t3o 8 (by decide) (by decide),
      t3o 19 (by decide) (by decide), t5v 9 (by decide) (by decide) (by decide),
      t5v 19 (by decide) (by decide) (by decide), z2v, v8, v9, e2s 3 (by decide), e2s 4 (by decide),
      e2s 5 (by decide), affPt_eq, entry_eq _ 0 rfl]
    rfl
  have fk : ∀ r, r ∉ .x30 :: fclob → r ∉ [Reg.x19, .x9] → t7.gpr r = t5.gpr r := fun r h1 h2 => by
    rw [k7.1 r h2, k6.regs.1 r h1]
  have hk35 : FKeep base t2 t5 := k3.trans k5
  have bits7 : Bits n base k t7.mem := by
    rw [m7]
    exact bits_of_out2 hn hs5
      (VG.Proof.X448.AArch64.Base.Bits.of_fkeep hn hs3 (VG.Proof.X448.AArch64.Base.Bits.of_fkeep hn hs2 bits2 k3) k5)
      k6.mem
  refine ⟨by omega, hs7, by rw [m7]; exact b6, by rw [m7]; exact z6, c7, bits7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show pt (EV t7.mem base) 0 1 2 = pt (EV t6.mem base) 0 1 2 by rw [m7], pA]
    have := addPt_rep hodd (baseEntry_ok j (nib k (2 * j + 1)) (by omega) no)
    rw [acc_step] at this
    exact this
  · rw [show pt (EV t7.mem base) 3 4 5 = pt (EV t6.mem base) 3 4 5 by rw [m7], pB]
    have := addPt_rep heven (baseEntry_ok j (nib k (2 * j)) (by omega) ne)
    rw [acc_step] at this
    exact this
  · rw [vn7 .v8 (by decide), k6.v .v8 (by decide), v5' .v8 (by decide), v3 .v8 (by decide), v2 .v8 (by decide),
      v1 .v8 (by decide)]
    exact hlane
  · rw [fk .x20 (by decide) (by decide), k5.regs.1 .x20 (by decide), k3.regs.1 .x20 (by decide),
      h2.2.2.1 .x20 (by decide), d1.keeps.1 .x20 (by decide)]; exact hout
  · rw [k7.2.1, k6.regs.2.1, k5.regs.2.1, k3.regs.2.1, h2.2.2.2.1, d1.keeps.2.1]; exact hrd
  · rw [k7.2.2, k6.regs.2.2, k5.regs.2.2, k3.regs.2.2, h2.2.2.2.2, d1.keeps.2.2]; exact hwr
  · rw [m7]
    refine Outside2.trans hmem ?_
    rw [← m1]
    exact (((VG.Proof.X448.AArch64.Base.Selected.outside2 h2).trans k3.mem).trans k5.mem).trans k6.mem
  · refine htbl.of_outside2 (by rw [k7.2.1, k6.regs.2.1, k5.regs.2.1, k3.regs.2.1,
      h2.2.2.2.1, d1.keeps.2.1, k7.2.2, k6.regs.2.2, k5.regs.2.2, k3.regs.2.2,
      h2.2.2.2.2, d1.keeps.2.2]) ?_
    rw [m7, ← m1]
    exact (((VG.Proof.X448.AArch64.Base.Selected.outside2 h2).trans k3.mem).trans k5.mem).trans k6.mem

/-- **The comb's loop, calling the additions**, as `loop_ok`: `StepInv` from step 0 to `n`, with
the return address kept in a lane of `v8` across it. -/
theorem combLoop_ok {n : Nat} (hn : n ≤ 57) (hn1 : 1 ≤ n) {s₀ s : State} {base : Addr} {k : Nat}
    (h : StepInv n s₀ base k 0 s) (hsy : s.syms = s₀.syms) :
    WP isa (combLoop n) s fun t => StepInv n s₀ base k n t := by
  unfold combLoop
  rw [WP.seq_iff]
  refine WP.mono_syms (insOf_ok [(.x30, .v8, 0)] s (by decide) (by decide))
    fun t₁ ⟨g₁, m₁, r₁, w₁, _, l₁, _⟩ sy₁ => ?_
  have h₁ : StepInvC n s₀ base k 0 t₁ :=
    ⟨h.bound, h.scr.of_keeps (rs := []) ⟨fun r _ => by rw [g₁], r₁, w₁⟩ (by decide), m₁ ▸ h.env, m₁ ▸ h.zero,
      by rw [g₁]; exact h.counter, m₁ ▸ h.bits, m₁ ▸ h.odd, m₁ ▸ h.even,
      (l₁ _ List.mem_cons_self).trans h.lr, by rw [g₁]; exact h.out, by rw [r₁]; exact h.rd,
      by rw [w₁]; exact h.wr, m₁ ▸ h.mem,
      h.tbl.of_far (by rw [r₁, w₁]) fun x _ => by rw [m₁]⟩
  rw [WP.seq_iff]
  refine WP.mono (WP.loop (M := isa) (body := combStep n) (c := .nonzero .x .x9)
    (Q := fun t => StepInvC n s₀ base k n t)
    (fun m (t : State) => 1 ≤ m ∧ m ≤ n ∧ StepInvC n s₀ base k (n - m) t ∧ t.syms = s₀.syms) ?_ n t₁
    ⟨hn1, le_refl _, by rw [Nat.sub_self]; exact h₁, sy₁.trans hsy⟩) fun t ht => ?_
  · intro m t ⟨h1, h2, ht, htsy⟩
    refine WP.mono_syms (combStep_ok hn ht (by omega) htsy) fun u ⟨hz, hu⟩ usy => ?_
    simp only [eval, State.read, BitVec.setWidth_eq, hz]
    by_cases hm : m = 1
    · subst hm
      rw [show n - 1 + 1 = n by omega] at hu ⊢
      exact .inl ⟨by simp, hu⟩
    · refine .inr ⟨congrArg some (decide_eq_true (by omega)), m - 1, by omega, by omega, by omega, ?_,
        usy.trans htsy⟩
      rw [show n - (m - 1) = n - m + 1 by omega]
      exact hu
  · refine WP.mono (umovOf_ok [(.x30, .v8, 0)] t (by decide) (by decide)) fun u ⟨um, ur, uw, _, ul, uo⟩ => ?_
    have ku : Keeps [.x30] t u := ⟨fun r hr => uo r (by simpa using hr), ur, uw⟩
    exact ⟨ht.bound, ht.scr.of_keeps ku (by decide), um ▸ ht.env, um ▸ ht.zero,
      by rw [ku.1 _ (by decide)]; exact ht.counter, um ▸ ht.bits, um ▸ ht.odd, um ▸ ht.even,
      (ul _ List.mem_cons_self).trans ht.lane, by rw [ku.1 _ (by decide)]; exact ht.out,
      by rw [ur]; exact ht.rd, by rw [uw]; exact ht.wr, um ▸ ht.mem,
      ht.tbl.of_far (by rw [ur, uw]) fun x _ => by rw [um]⟩

end VG.Proof.Ed448.AArch64.Point56
