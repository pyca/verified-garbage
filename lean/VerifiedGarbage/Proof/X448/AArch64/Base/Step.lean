import VerifiedGarbage.Proof.X448.AArch64.Base.Negate
import VerifiedGarbage.Proof.X448.AArch64.Base.AddEnv

/-!
# X448 of the base point on AArch64: one step of the comb

Untrusted: everything here is checked by Lean. Step `j` reads both digits,
selects table `j`'s entries, negates each for a negative digit and adds it to
its accumulator: the invariant `StepInv` (as Ed25519's `CombInv`) holds for
`j + 1` after the step if it held for `j`.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env opSwap)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (nib mag)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The entries' slots. -/
def entrySlots : List Index := [6, 7, 8, 9]

theorem slot_entry (i : Index) : i ∈ entrySlots ↔ OX ≤ slot i.val ∧ slot i.val < OX + 512 := by
  have := i.isLt
  simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false, OX, slot, Fin.ext_iff]
  omega

/-- A selection, in the slot environment. -/
theorem selected_env {s t : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {j ao ae : Nat}
    (h : Selected base j ao ae s t) :
    BEnv t.mem base ∧ Same base entrySlots s.mem t.mem ∧
    EV t.mem base 6 = (Impl.X448.baseTable j ao).1 ∧ EV t.mem base 7 = (Impl.X448.baseTable j ao).2 ∧
    EV t.mem base 8 = (Impl.X448.baseTable j ae).1 ∧ EV t.mem base 9 = (Impl.X448.baseTable j ae).2 ∧
    (∀ i ∈ entrySlots, Bnd Mb t.mem base (slot i.val)) := by
  obtain ⟨hv, hf, _⟩ := h
  have hn := hs.nowrap
  -- Words outside the entries' slots are kept.
  have keep : ∀ i : Index, i ∉ entrySlots → ∀ w < 8, limbs t.mem base (slot i.val) w = limbs s.mem base (slot i.val) w :=
    fun i hi w hw => by
      have := i.isLt
      have hi' := (slot_entry i).not.mp hi
      simp only [OX, slot] at hi'
      exact congrArg BitVec.toNat (hf.word (by simp only [OX, slot]; omega) (by simp only [slot]; omega))
  -- The entries' limbs.
  have lv : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, word t.mem base (o + 8 * w) = limb v w) →
      (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) := fun v o h w hw => by
    show (word t.mem base (o + 8 * w)).toNat = _; rw [h w hw]
  have l6 := lv _ OX fun w hw => (hv w hw).1
  have l8 := lv _ EX fun w hw => (hv w hw).2.1
  have l7 := lv _ OY fun w hw => (hv w hw).2.2.1
  have l9 := lv _ EY fun w hw => (hv w hw).2.2.2
  have fe : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) →
      VG.Proof.X448.AArch64.Weak.F t.mem base o = v := fun v o h => by
    simp only [VG.Proof.X448.AArch64.Weak.F]
    rw [VG.Proof.X448.Wide.valN_congr h, limb_val, VG.Proof.X448.toFe_self]
  have bd : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) →
      Bnd Mb t.mem base o := fun v o h w hw => by
    rw [h w hw]; exact Nat.lt_of_lt_of_le (limb_lt v w) (by decide)
  refine ⟨fun i => ?_, keep, fe _ _ l6, fe _ _ l7, fe _ _ l8, fe _ _ l9, ?_⟩
  · by_cases hi : i ∈ entrySlots
    · simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l6 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l7 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l8 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l9 w hw) (by decide)
    · intro w hw; rw [keep i hi w hw]; exact hb i w hw
  · intro i hi
    simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact bd _ _ l6
    · exact bd _ _ l7
    · exact bd _ _ l8
    · exact bd _ _ l9

/-! ## The invariant -/

open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Proof.X448 (oddSumZ evenSumZ combG)

/-- The state of a comb of `n` tables before step `j` (of the scalar `k`), from the function's
state after its setup `s₀`. -/
structure StepInv (n : Nat) (s₀ : State) (base : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ n
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  bits : Bits n base k s.mem
  odd : Rep (pt (EV s.mem base) 0 1 2) (((combG n : ℤ) + oddSumZ k j) • baseAff)
  even : Rep (pt (EV s.mem base) 3 4 5) (((combG n : ℤ) + evenSumZ k j) • baseAff)
  lr : s.gpr .x30 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem
  tbl : TblAt s base (s₀.syms combSym)
  keep : ∀ r, r ∉ .x1 :: .x19 :: VG.Proof.X448.AArch64.Fast.fclob → s.gpr r = s₀.gpr r

/-- What every phase after the setup keeps. -/
structure Frame (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  lr : s.gpr .x30 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem

theorem StepInv.frame {n : Nat} {s₀ s : State} {base : Addr} {k j : Nat} (h : StepInv n s₀ base k j s) :
    Frame s₀ base s := ⟨h.scr, h.env, h.zero, h.lr, h.out, h.rd, h.wr, h.mem⟩

/-- What the comb needs before its accumulators are set: the working space, every slot's limbs
below `Ib`, slot 19 zero, the bits of `k` and the tables. -/
structure CombPre (n : Nat) (base : Addr) (k : Nat) (s : State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  bits : Bits n base k s.mem
  tbl : TblAt s base (s.syms combSym)

/-! ## One step -/

open VG.Proof.X448 (addPt addPt_rep basePt negAff baseEntry_ok nib_lt mag_lt sdig)

theorem step_eq : VG.Impl.X448.AArch64.Base.stepR =
    .seq (.block digits) (.seq (.block select) (.block (
      negate (slot (6 : Index).val) (BITS + 4) (slot (10 : Index).val) ++
      (addAffine (slot (0 : Index).val) (slot (1 : Index).val) (slot (2 : Index).val)
        (slot (6 : Index).val) (slot (7 : Index).val) ++
      (negate (slot (8 : Index).val) BITS (slot (10 : Index).val) ++
      (addAffine (slot (3 : Index).val) (slot (4 : Index).val) (slot (5 : Index).val)
        (slot (8 : Index).val) (slot (9 : Index).val) ++
      ([.addImm .x .x19 .x19 1, .sub .x .x9 .x19 .x30] : List Instr))))))) := by
  simp only [VG.Impl.X448.AArch64.Base.stepR, List.append_assoc]; rfl

/-- The selected scalar slots outside `entrySlots` are kept by a selection. -/
theorem Selected.outside2 {base : Addr} {j ao ae : Nat} {s t : State} (h : Selected base j ao ae s t) :
    Outside2 base 64 2816 ACC 1152 s.mem t.mem := fun x h1 _ =>
  h.2.1 x (by simp only [OX, slot] at h1 ⊢; omega)

/-- The entry for the digit `n - 8`, negated as `negate` does. -/
theorem entry_eq (e : Spec.X448.Fe × Spec.X448.Fe) (z : Spec.X448.Fe) (hz : z = 0) (n : Nat) :
    (⟨if decide (n < 8) then z - e.1 else e.1, e.2, 1⟩ : Spec.Ed448.Point) =
      basePt (if n < 8 then negAff e else e) := by
  subst hz
  by_cases hn : n < 8
  · simp only [hn, decide_true, ↓reduceIte]; rfl
  · simp only [hn, decide_false, ↓reduceIte, Bool.false_eq_true]; rfl

theorem acc_step (G : ℤ) (S : ℤ) (n j : Nat) :
    (G + S) • baseAff + (((n : ℤ) - 8) * 256 ^ j) • baseAff = (G + (S + ((n : ℤ) - 8) * 256 ^ j)) • baseAff := by
  rw [← add_smul, add_assoc]

/-- The tables survive what keeps the regions and changes only the scalar slots and `ACC`. -/
theorem TblAt.of_outside2 {s t : State} {base T : Addr} (h : TblAt s base T)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (hm : Outside2 base 64 2816 ACC 1152 s.mem t.mem) :
    TblAt t base T :=
  h.of_far hrw fun x hx => hm x (by omega) (by simp only [ACC]; omega)

theorem notin_keep {l : List Reg} (h : ∀ q ∈ l, q ∈ .x1 :: .x19 :: VG.Proof.X448.AArch64.Fast.fclob)
    {r : Reg} (hr : r ∉ .x1 :: .x19 :: VG.Proof.X448.AArch64.Fast.fclob) : r ∉ l := fun e => hr (h r e)

theorem step_ok {n : Nat} (hn : n ≤ 57) {s₀ s : State} {base : Addr} {k j : Nat}
    (h : StepInv n s₀ base k j s) (hj : j < n) (hsy : s.syms = s₀.syms) (h30 : s₀.gpr .x30 = BitVec.ofNat 64 n) :
    WP isa VG.Impl.X448.AArch64.Base.stepR s fun t =>
      (t.gpr .x9 != 0) = decide (j + 1 ≠ n) ∧ StepInv n s₀ base k (j + 1) t := by
  obtain ⟨_, hs, hb, hz, hc, hbits, hodd, heven, hlr, hout, hrd, hwr, hmem, htbl, hkeep⟩ := h
  have no := nib_lt k (2 * j + 1)
  have ne := nib_lt k (2 * j)
  rw [step_eq]
  -- The digits.
  refine WP.seq (WP.mono_syms (digits_ok hs hn hj hc hbits) fun t1 ⟨d1, m1⟩ sy1 => ?_)
  have hs1 : Scr t1 base := hs.of_keeps d1.keeps (by decide)
  have hb1 : BEnv t1.mem base := by rw [m1]; exact hb
  have hm1 : Masks (mag (nib k (2 * j + 1))) (mag (nib k (2 * j))) t1 :=
    ⟨d1.oddMask, d1.evenMask, d1.oddZero, d1.evenZero⟩
  have hc1 : t1.gpr .x19 = BitVec.ofNat 64 j := by rw [d1.keeps.1 _ (by decide)]; exact hc
  -- The selection.
  have tb1 : TblAt t1 base (s₀.syms combSym) :=
    htbl.of_far (by rw [d1.keeps.2.1, d1.keeps.2.2]) fun x _ => by rw [m1]
  refine WP.seq (WP.mono (select_ok hs1 tb1 (by rw [sy1, hsy]) (by omega) hc1 (mag_lt no) (mag_lt ne)
    hm1) fun t2 (h2 : Selected base j _ _ t1 t2) => ?_)
  obtain ⟨b2, s2, v6, v7, v8, v9, bnd2⟩ := selected_env hs1 hb1 h2
  have hs2 : Scr t2 base := hs1.of_keeps h2.2.2 (by decide)
  have hc2 : t2.gpr .x19 = BitVec.ofNat 64 j := by rw [h2.2.2.1 _ (by decide)]; exact hc1
  have bits2 : Bits n base k t2.mem := fun q hq => by
    have hn := hs.nowrap
    rw [h2.2.1 _ (by rw [ofs_off0 base (by simp only [BITS]; omega)]; simp only [OX, BITS, slot]; omega), m1]
    exact hbits q hq
  have z2 : ∀ w < 8, limbs t2.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s2 19 (by decide) w hw]; rw [m1]; exact hz w hw
  have e1 : EV t1.mem base = EV s.mem base := by rw [m1]
  -- The odd digit's entry, negated, and added to `A`.
  rw [WP.block_append_iff]
  refine WP.mono (negate_ok hs2 b2 (k := k) (i := 2 * j + 1) (o := BITS + 4) 6 (by decide) hn (by omega) (by omega)
    (by simp only [BITS]; omega) (by simp only [BITS]; omega) hc2 bits2 (bnd2 6 (by decide))
    (zero_env z2).2) fun t3 ⟨k3, b3, s3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  have z3 : ∀ w < 8, limbs t3.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s3 19 (by decide) w hw]; exact z2 w hw
  rw [WP.block_append_iff]
  refine WP.mono (addAffine_ok 0 1 2 6 7 (by decide) (by decide) (by decide) hs3 b3 (zero_env z3).2
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)) (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)) (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)))
    fun t4 ⟨k4, b4, s4, _, _, _, e4⟩ => ?_
  have hs4 := k4.scr hs3
  have z4 : ∀ w < 8, limbs t4.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s4 19 (by decide) w hw]; exact z3 w hw
  have hc4 : t4.gpr .x19 = BitVec.ofNat 64 j := by
    rw [k4.regs.1 .x19 (by decide), k3.regs.1 .x19 (by decide)]; exact hc2
  -- The even digit's entry, negated, and added to `B`.
  rw [WP.block_append_iff]
  refine WP.mono (negate_ok hs4 b4 (k := k) (i := 2 * j) (o := BITS) 8 (by decide) hn (by omega) (by omega)
    (by omega) (by simp only [BITS]; omega) hc4
    (Bits.of_fkeep hn hs3 (Bits.of_fkeep hn hs2 bits2 k3) k4)
    (s4.bnd (by decide) (s3.bnd (by decide) (bnd2 8 (by decide)))) (zero_env z4).2)
    fun t5 ⟨k5, b5, s5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  have z5 : ∀ w < 8, limbs t5.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s5 19 (by decide) w hw]; exact z4 w hw
  rw [WP.block_append_iff]
  refine WP.mono (addAffine_ok 3 4 5 8 9 (by decide) (by decide) (by decide) hs5 b5 (zero_env z5).2
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)) (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)) (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)))
    fun t6 ⟨k6, b6, s6, _, _, _, e6⟩ => ?_
  have hs6 := k6.scr hs5
  -- The counter.
  have hc6 : t6.gpr .x19 = BitVec.ofNat 64 j := by
    rw [k6.regs.1 .x19 (by decide), k5.regs.1 .x19 (by decide)]; exact hc4
  have h6 : t6.gpr .x30 = BitVec.ofNat 64 n := by
    rw [k6.regs.1 .x30 (by decide), k5.regs.1 .x30 (by decide), k4.regs.1 .x30 (by decide),
      k3.regs.1 .x30 (by decide), h2.2.2.1 .x30 (by decide), d1.keeps.1 .x30 (by decide), hkeep .x30 (by decide), h30]
  refine WP.mono (nextR_ok t6 hn hj hc6 h6) fun t7 ⟨c7, n7, k7, m7⟩ => ⟨n7, ?_⟩
  have hs7 : Scr t7 base := hs6.of_keeps k7 (by decide)
  have z6 : ∀ w < 8, limbs t6.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s6 19 (by decide) w hw]; exact z5 w hw
  -- Values of the slots along the way.
  have e2s : ∀ i : Index, i ∉ entrySlots → EV t2.mem base i = EV s.mem base i := fun i hi => by
    rw [Same.env s2 hi, e1]
  have z2v : EV t2.mem base 19 = 0 := (zero_env z2).1
  have t3o : ∀ i : Index, i ≠ 6 → i ≠ 10 → EV t3.mem base i = EV t2.mem base i := fun i h6 h10 => by
    rw [e3]; simp only [opSwap, Function.update_apply, h6, h10, ite_false]
  have t36 : EV t3.mem base 6 =
      if decide (nib k (2 * j + 1) < 8) then EV t2.mem base 19 - EV t2.mem base 6 else EV t2.mem base 6 := by
    rw [e3]; simp only [opSwap, Function.update_apply, show (6 : Index) ≠ 10 by decide, ite_false, ite_true]
  have t5o : ∀ i : Index, i ≠ 8 → i ≠ 10 → EV t5.mem base i = EV t4.mem base i := fun i h8 h10 => by
    rw [e5]; simp only [opSwap, Function.update_apply, h8, h10, ite_false]
  have t58 : EV t5.mem base 8 =
      if decide (nib k (2 * j) < 8) then EV t4.mem base 19 - EV t4.mem base 8 else EV t4.mem base 8 := by
    rw [e5]; simp only [opSwap, Function.update_apply, show (8 : Index) ≠ 10 by decide, ite_false, ite_true]
  have t4s : ∀ i : Index, i ∉ temps ++ [2, 0, 1] → i ∉ [10] ++ [6, 10] →
      EV t4.mem base i = EV t2.mem base i := fun i h4 h3 => by
    rw [Same.env s4 h4, Same.env s3 h3]
  -- The odd accumulator.
  have pA : pt (EV t4.mem base) 0 1 2 = addPt (pt (EV s.mem base) 0 1 2)
      (basePt (if nib k (2 * j + 1) < 8 then negAff (Impl.X448.baseTable j (mag (nib k (2 * j + 1))))
        else Impl.X448.baseTable j (mag (nib k (2 * j + 1))))) := by
    rw [e4, affEnv_A, t3o 0 (by decide) (by decide), t3o 1 (by decide) (by decide),
      t3o 2 (by decide) (by decide), t36, t3o 7 (by decide) (by decide), t3o 19 (by decide) (by decide),
      z2v, v6, v7, e2s 0 (by decide), e2s 1 (by decide), e2s 2 (by decide), affPt_eq,
      entry_eq _ 0 rfl]
    rfl
  have pB : pt (EV t6.mem base) 3 4 5 = addPt (pt (EV s.mem base) 3 4 5)
      (basePt (if nib k (2 * j) < 8 then negAff (Impl.X448.baseTable j (mag (nib k (2 * j))))
        else Impl.X448.baseTable j (mag (nib k (2 * j))))) := by
    rw [e6, affEnv_B, t5o 3 (by decide) (by decide), t5o 4 (by decide) (by decide),
      t5o 5 (by decide) (by decide), t58, t5o 9 (by decide) (by decide), t5o 19 (by decide) (by decide),
      t4s 3 (by decide) (by decide), t4s 4 (by decide) (by decide), t4s 5 (by decide) (by decide),
      t4s 8 (by decide) (by decide), t4s 9 (by decide) (by decide), t4s 19 (by decide) (by decide),
      z2v, v8, v9, e2s 3 (by decide), e2s 4 (by decide), e2s 5 (by decide), affPt_eq,
      entry_eq _ 0 rfl]
    rfl
  have p7A : pt (EV t7.mem base) 0 1 2 = pt (EV t4.mem base) 0 1 2 := by
    simp only [pt, m7]
    rw [Same.env s6 (i := 0) (by decide), Same.env s5 (i := 0) (by decide),
      Same.env s6 (i := 1) (by decide), Same.env s5 (i := 1) (by decide),
      Same.env s6 (i := 2) (by decide), Same.env s5 (i := 2) (by decide)]
  have p7B : pt (EV t7.mem base) 3 4 5 = pt (EV t6.mem base) 3 4 5 := by simp only [pt, m7]
  refine ⟨by omega, hs7, by rw [m7]; exact b6, by rw [m7]; exact z6, c7,
    by rw [m7]; exact Bits.of_fkeep hn hs5 (Bits.of_fkeep hn hs4 (Bits.of_fkeep hn hs3 (Bits.of_fkeep hn hs2 bits2 k3) k4) k5) k6,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p7A, pA]
    have := addPt_rep hodd (baseEntry_ok j (nib k (2 * j + 1)) (by omega) no)
    rw [acc_step] at this
    exact this
  · rw [p7B, pB]
    have := addPt_rep heven (baseEntry_ok j (nib k (2 * j)) (by omega) ne)
    rw [acc_step] at this
    exact this
  · rw [k7.1 .x30 (by decide), k6.regs.1 .x30 (by decide), k5.regs.1 .x30 (by decide),
      k4.regs.1 .x30 (by decide), k3.regs.1 .x30 (by decide), h2.2.2.1 .x30 (by decide),
      d1.keeps.1 .x30 (by decide)]; exact hlr
  · rw [k7.1 .x20 (by decide), k6.regs.1 .x20 (by decide), k5.regs.1 .x20 (by decide),
      k4.regs.1 .x20 (by decide), k3.regs.1 .x20 (by decide), h2.2.2.1 .x20 (by decide),
      d1.keeps.1 .x20 (by decide)]; exact hout
  · rw [k7.2.1, k6.regs.2.1, k5.regs.2.1, k4.regs.2.1, k3.regs.2.1, h2.2.2.2.1, d1.keeps.2.1]; exact hrd
  · rw [k7.2.2, k6.regs.2.2, k5.regs.2.2, k4.regs.2.2, k3.regs.2.2, h2.2.2.2.2, d1.keeps.2.2]; exact hwr
  · rw [m7]
    refine Outside2.trans hmem ?_
    rw [← m1]
    exact (((h2.outside2.trans k3.mem).trans k4.mem).trans k5.mem).trans k6.mem
  · refine htbl.of_outside2 (by rw [k7.2.1, k6.regs.2.1, k5.regs.2.1, k4.regs.2.1, k3.regs.2.1,
      h2.2.2.2.1, d1.keeps.2.1, k7.2.2, k6.regs.2.2, k5.regs.2.2, k4.regs.2.2, k3.regs.2.2,
      h2.2.2.2.2, d1.keeps.2.2]) ?_
    rw [m7, ← m1]
    exact (((h2.outside2.trans k3.mem).trans k4.mem).trans k5.mem).trans k6.mem
  · intro r hr
    rw [k7.1 r (notin_keep (by decide) hr), k6.regs.1 r (notin_keep (by decide) hr),
      k5.regs.1 r (notin_keep (by decide) hr), k4.regs.1 r (notin_keep (by decide) hr),
      k3.regs.1 r (notin_keep (by decide) hr), h2.2.2.1 r (notin_keep (by decide) hr),
      d1.keeps.1 r (notin_keep (by decide) hr)]
    exact hkeep r hr

/-! ## The steps -/

theorem loop_ok {n : Nat} (hn : n ≤ 57) {s₀ : State} {base : Addr} {k : Nat}
    (h30 : s₀.gpr .x30 = BitVec.ofNat 64 n) :
    ∀ m, ∀ s, 1 ≤ m → m ≤ n → StepInv n s₀ base k (n - m) s → s.syms = s₀.syms →
      WP isa (.loop VG.Impl.X448.AArch64.Base.stepR (.nonzero .x .x9)) s fun t =>
        StepInv n s₀ base k n t := by
  intro m s h1 h2 hi hsy
  refine WP.loop (M := isa) (body := VG.Impl.X448.AArch64.Base.stepR) (c := .nonzero .x .x9)
    (Q := fun t => StepInv n s₀ base k n t)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ n ∧ StepInv n s₀ base k (n - m) s ∧ s.syms = s₀.syms) ?_ m s
    ⟨h1, h2, hi, hsy⟩
  intro m s ⟨h1, h2, hi, hsy⟩
  refine WP.mono_syms (step_ok hn hi (by omega) hsy h30) fun t ⟨hz, ht⟩ tsy => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, hz]
  by_cases hm : m = 1
  · subst hm
    rw [show n - 1 + 1 = n by omega] at ht ⊢
    exact .inl ⟨by simp, ht⟩
  · refine .inr ⟨congrArg some (decide_eq_true (by omega)), m - 1, by omega, by omega, by omega, ?_,
      tsy.trans hsy⟩
    rw [show n - (m - 1) = n - m + 1 by omega]
    exact ht

end VG.Proof.X448.AArch64.Base
