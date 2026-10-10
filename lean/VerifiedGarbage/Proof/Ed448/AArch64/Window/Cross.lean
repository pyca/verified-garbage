import VerifiedGarbage.Proof.Ed448.AArch64.Window.Window
import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call

/-!
# Ed448 verification on AArch64: the points compared

Untrusted: everything here is checked by Lean. `wcross`, after the windows:
`Q = [k](-A) + [S]B` (slots 3–5 plus slots 0–2, copied to 6–8, by a call of
`vg_ed448_r56_point_add`), doubled twice and copied to slots 0–2, `R` from `RX`
and `RY` into slots 3–5 (`Z = 1`), doubled twice (calls of
`vg_ed448_r56_point_double`), and the products `X_Q Z_R`, `X_R Z_Q`,
`Y_Q Z_R`, `Y_R Z_Q` into slots 12–15 (`wcross_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot limb)
open VG.Impl.X448.AArch64.Fast (ops codeOf)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same block_codeOf ops_append mulOp)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genEnv genPt temps addOps_ok zero_env constSlot_ok bnd_of_words F_of_words)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

/-- Two doublings. -/
def dbl2 (p : Point) : Point := VG.Proof.Ed448.double (VG.Proof.Ed448.double p)

/-- What `wcross` leaves in slots 12–15, for `Q` and `R`. -/
structure Cross (Q R : Point) (e : Env) : Prop where
  c12 : e 12 = (dbl2 Q).X * (dbl2 R).Z
  c13 : e 13 = (dbl2 R).X * (dbl2 Q).Z
  c14 : e 14 = (dbl2 Q).Y * (dbl2 R).Z
  c15 : e 15 = (dbl2 R).Y * (dbl2 Q).Z

theorem addPt_comm (p q : Point) : addPt p q = addPt q p := by
  simp only [addPt, Fin.mul_comm]
  rw [AddCommMagma.add_comm (q.X * p.Y)]

/-- Three slots copied from three others, among bounded ones: the copies' limbs, and every
other slot's kept. -/
theorem copy3_ok {s : State} {base : Addr} (hs : Scr s base) (o a : Nat) (ho : o + 3 ≤ 22) (ha : a + 3 ≤ 22)
    (hsep : o + 3 ≤ a ∨ a + 3 ≤ o) :
    WP isa (.block (Impl.Curve448.AArch64.copy (slot o) (slot a) ++ Impl.Curve448.AArch64.copy (slot (o + 1))
        (slot (a + 1)) ++ Impl.Curve448.AArch64.copy (slot (o + 2)) (slot (a + 2)))) s fun t =>
      (∀ c < 3, ∀ j < 8, limbs t.mem base (slot (o + c)) j = limbs s.mem base (slot (a + c)) j) ∧
      (∀ i : Index, (i.val < o ∨ o + 3 ≤ i.val) → ∀ j < 8, limbs t.mem base (slot i.val) j =
        limbs s.mem base (slot i.val) j) ∧
      Outside base (slot o) 384 s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyS_ok hs (o := slot o) (a := slot a) (by simp only [slot]; omega) (by simp only [slot]; omega)
    (by simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot]; omega)) fun t1 ⟨v1, o1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (copyS_ok hs1 (o := slot (o + 1)) (a := slot (a + 1)) (by simp only [slot]; omega)
    (by simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot]; omega)
    (by simp only [slot]; omega)) fun t2 ⟨v2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  refine WP.mono (copyS_ok hs2 (o := slot (o + 2)) (a := slot (a + 2)) (by simp only [slot]; omega)
    (by simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot]; omega)
    (by simp only [slot]; omega)) fun t ⟨v3, o3, k3⟩ => ⟨fun c hc j hj => ?_, fun i hi j hj => ?_, ?_,
      (k1.trans k2).trans k3⟩
  · rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
    · rw [o3.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
        o2.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega), Nat.add_zero, v1 j hj,
        Nat.add_zero]
    · rw [o3.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega), v2 j hj,
        o1.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)]
    · rw [v3 j hj, o2.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
        o1.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)]
  · have := i.isLt
    rw [o3.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o2.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o1.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)]
  · intro x hx
    rw [o3 x (by simp only [slot] at hx ⊢; omega), o2 x (by simp only [slot] at hx ⊢; omega),
      o1 x (by simp only [slot] at hx ⊢; omega)]

theorem pt_of_limbs {m m' : Mem} {base : Addr} {o a : Nat}
    (h : ∀ c < 3, ∀ j < 8, limbs m' base (slot (o + c)) j = limbs m base (slot (a + c)) j)
    {x y z x' y' z' : Index} (hx : x.val = o) (hy : y.val = o + 1) (hz : z.val = o + 2) (hx' : x'.val = a)
    (hy' : y'.val = a + 1) (hz' : z'.val = a + 2) : pt (EV m' base) x y z = pt (EV m base) x' y' z' := by
  simp only [pt, VG.Proof.X448.AArch64.Weak.E]
  rw [hx, hy, hz, hx', hy', hz']
  rw [FV_of_limbs (o := slot a) (o' := slot o) (fun j hj => by simpa using h 0 (by decide) j hj),
    FV_of_limbs (h 1 (by decide)), FV_of_limbs (h 2 (by decide))]

/-- The registers `wcross` may write. -/
def crossClob : List Reg := .x30 :: .x4 :: VG.Proof.Curve448.AArch64.Fast.clob ++ VG.Proof.X448.AArch64.clob

theorem crossClob_ckeep {s t : State} {base : Addr} (h : Point56.CKeep base s t) : Keeps crossClob s t :=
  h.regs.mono fun _ hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hr))

theorem crossClob_clob {s t : State} (h : Keeps VG.Proof.X448.AArch64.clob s t) : Keeps crossClob s t :=
  h.mono fun _ hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hr))

theorem bnd_copy {m m' : Mem} {base : Addr} {o a : Nat} {n : Nat}
    (h : ∀ j < 8, limbs m' base o j = limbs m base a j) (hb : Bnd n m base a) : Bnd n m' base o := fun j hj => by
  rw [h j hj]; exact hb j hj

/-- **The points compared**: `Q = [S]B + [k](-A)` and `R` (from `RX` and `RY`), doubled twice,
cross-multiplied into slots 12–15. -/
theorem wcross_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hz : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0) (h20 : EV s.mem base 20 = 1)
    (hrx : ∀ i < 8, limbs s.mem base RX i < Ib) (hry : ∀ i < 8, limbs s.mem base RY i < Ib) :
    WP isa wcross s fun t =>
      Scr t base ∧ Keeps crossClob s t ∧ Outside2 base 64 2816 ACC 1152 s.mem t.mem ∧
      Cross (addPt (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 3 4 5)) ⟨FV s.mem base RX, FV s.mem base RY, 1⟩
        (EV t.mem base) ∧
      (∀ i : Index, 12 ≤ i.val → i.val < 16 → Bnd Mb t.mem base (slot i.val)) := by
  unfold wcross
  -- `[S]B` copied to slots 6–8.
  rw [WP.seq_iff]
  refine WP.mono (copy3_ok hs 6 0 (by decide) (by decide) (by decide)) fun t1 ⟨v1, o1, f1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have b1 : BEnv t1.mem base := fun i => by
    by_cases h : i.val < 6 ∨ 9 ≤ i.val
    · exact bnd_copy (o1 i h) (hb i)
    · have : i.val = 6 + (i.val - 6) := by omega
      exact fun j hj => by
        show limbs t1.mem base (slot i.val) j < Ib
        rw [this, v1 _ (by omega) j hj]; exact hb ⟨0 + (i.val - 6), by omega⟩ j hj
  have z1 : ∀ w < 8, limbs t1.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [o1 19 (by decide) w hw]; exact hz w hw
  have e1 : ∀ i : Index, (i.val < 6 ∨ 9 ≤ i.val) → EV t1.mem base i = EV s.mem base i := fun i hi =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (o1 i hi))
  -- `Q`, added.
  rw [WP.seq_iff]
  refine WP.mono (Point56.addCall_ok hs1 b1 (zero_env z1).2) fun t2 ⟨k2, b2, s2, _, _, m2, e2, _⟩ => ?_
  have hs2 := k2.scr hs1
  have q2 : pt (EV t2.mem base) 3 4 5 = addPt (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 3 4 5) := by
    rw [e2, Point56.genEnv_pt, (zero_env z1).1, VG.Proof.X448.AArch64.Base.genPt_eq, addPt_comm,
      pt_of_limbs (x := 6) (y := 7) (z := 8) (x' := 0) (y' := 1) (z' := 2) v1 rfl rfl rfl rfl rfl rfl]
    simp only [pt]
    rw [e1 3 (by decide), e1 4 (by decide), e1 5 (by decide)]
  have one2 : EV t2.mem base 20 = 1 := by
    rw [Same.env s2 (i := 20) (by decide), e1 20 (by decide)]; exact h20
  -- `Q`, doubled twice.
  rw [WP.seq_iff]
  refine WP.mono (Point56.doubleCall_ok hs2 b2 m2) fun t3 ⟨k3, b3, s3, _, _, m3, e3, _⟩ => ?_
  have hs3 := k3.scr hs2
  have one3 : EV t3.mem base 20 = 1 := by rw [Same.env s3 (i := 20) (by decide)]; exact one2
  rw [WP.seq_iff]
  refine WP.mono (Point56.doubleCall_ok hs3 b3 m3) fun t4 ⟨k4, b4, s4, _, _, _, e4, _⟩ => ?_
  have hs4 := k4.scr hs3
  have one4 : EV t4.mem base 20 = 1 := by rw [Same.env s4 (i := 20) (by decide)]; exact one3
  have q4 : pt (EV t4.mem base) 3 4 5 = dbl2 (addPt (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 3 4 5)) := by
    rw [e4, dblEnv_345, one3, dblPt_eq, e3, dblEnv_345, one2, dblPt_eq, q2]; rfl
  -- `Q` to slots 0–2, and `R` into slots 3–5.
  rw [WP.seq_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy3_ok hs4 0 3 (by decide) (by decide) (by decide)) fun t5 ⟨v5, o5, f5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  -- `RX` and `RY`, kept by every step so far.
  have mR : ∀ o, o = RX ∨ o = RY → ∀ i < 8, limbs t5.mem base o i = limbs s.mem base o i := fun o ho i hi => by
    have hn : o + 8 * i + 8 ≤ 8192 := by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN] <;> omega
    refine congrArg BitVec.toNat ?_
    rw [f5.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [slot, RX, RY, CAN] <;> omega)) hn,
      k4.mem.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN] <;> omega))
        (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN, ACC] <;> omega)) hn,
      k3.mem.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN] <;> omega))
        (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN, ACC] <;> omega)) hn,
      k2.mem.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN] <;> omega))
        (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN, ACC] <;> omega)) hn,
      f1.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [slot, RX, RY, CAN] <;> omega)) hn]
  refine WP.mono (copyS_ok hs5 (o := slot 3) (a := RX) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t6 ⟨v6, o6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  refine WP.mono (copyS_ok hs6 (o := slot 4) (a := RY) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t7 ⟨v7, o7, k7⟩ => ?_
  have hs7 := hs6.of_keeps k7 (by decide)
  refine WP.mono (constSlot_ok hs7 (o := slot 5) (by decide) (by decide) 1) fun t8 ⟨v8, o8, k8⟩ => ?_
  have hs8 := hs7.of_keeps k8 (by decide)
  have keep8 : ∀ i : Index, i ≠ 3 → i ≠ 4 → i ≠ 5 → ∀ j < 8,
      limbs t8.mem base (slot i.val) j = limbs t5.mem base (slot i.val) j := fun i h3 h4 h5 j hj => by
    have := i.isLt
    have n3 : i.val ≠ 3 := fun e => h3 (Fin.ext e)
    have n4 : i.val ≠ 4 := fun e => h4 (Fin.ext e)
    have n5 : i.val ≠ 5 := fun e => h5 (Fin.ext e)
    rw [o8.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o7.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o6.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)]
  have l3 : ∀ j < 8, limbs t8.mem base (slot 3) j = limbs s.mem base RX j := fun j hj => by
    rw [o8.limbs (by decide) (by decide) (by omega), o7.limbs (by decide) (by decide) (by omega), v6 j hj,
      mR _ (.inl rfl) j hj]
  have l4 : ∀ j < 8, limbs t8.mem base (slot 4) j = limbs s.mem base RY j := fun j hj => by
    rw [o8.limbs (by decide) (by decide) (by omega), v7 j hj,
      o6.limbs (by simp only [RY, CAN]; decide) (by simp only [RY, CAN]; decide) (by omega), mR _ (.inr rfl) j hj]
  have l0 : ∀ c < 3, ∀ j < 8, limbs t8.mem base (slot (0 + c)) j = limbs t4.mem base (slot (3 + c)) j :=
    fun c hc j hj => by
      rw [show limbs t8.mem base (slot (0 + c)) j = limbs t8.mem base (slot (⟨0 + c, by omega⟩ : Index).val) j
        from rfl, keep8 _ (by intro h; simp [Fin.ext_iff] at h; omega) (by intro h; simp [Fin.ext_iff] at h; omega)
        (by intro h; simp [Fin.ext_iff] at h; omega) j hj]
      exact v5 c hc j hj
  have b8 : BEnv t8.mem base := by
    intro i
    by_cases h3 : i = 3
    · subst h3; exact fun j hj => by show limbs t8.mem base (slot 3) j < Ib; rw [l3 j hj]; exact hrx j hj
    by_cases h4 : i = 4
    · subst h4; exact fun j hj => by show limbs t8.mem base (slot 4) j < Ib; rw [l4 j hj]; exact hry j hj
    by_cases h5 : i = 5
    · subst h5; exact bnd_of_words v8
    · refine fun j hj => ?_
      rw [keep8 i h3 h4 h5 j hj]
      by_cases h : i.val < 0 ∨ 0 + 3 ≤ i.val
      · rw [o5 i h j hj]; exact b4 i j hj
      · have : i.val = 0 + i.val := by omega
        show limbs t5.mem base (slot i.val) j < Ib
        rw [this, v5 _ (by omega) j hj]; exact b4 ⟨3 + i.val, by omega⟩ j hj
  have e8 : ∀ i : Index, i ≠ 3 → i ≠ 4 → i ≠ 5 → EV t8.mem base i = EV t5.mem base i := fun i h3 h4 h5 =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (keep8 i h3 h4 h5))
  have r8 : pt (EV t8.mem base) 3 4 5 = ⟨FV s.mem base RX, FV s.mem base RY, 1⟩ := by
    show (⟨FV t8.mem base (slot 3), FV t8.mem base (slot 4), FV t8.mem base (slot 5)⟩ : Point) = _
    rw [FV_of_limbs l3, FV_of_limbs l4, F_of_words v8]
  have q8 : pt (EV t8.mem base) 0 1 2 = dbl2 (addPt (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 3 4 5)) := by
    rw [pt_of_limbs (x := 0) (y := 1) (z := 2) (x' := 3) (y' := 4) (z' := 5) l0 rfl rfl rfl rfl rfl rfl, q4]
  have one8 : EV t8.mem base 20 = 1 := by
    rw [e8 20 (by decide) (by decide) (by decide)]
    rw [show EV t5.mem base 20 = EV t4.mem base 20 from
      congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (o5 20 (by decide)))]
    exact one4
  have z8 : Bnd Mb t8.mem base (slot (5 : Index).val) := fun j hj => by
    show (word t8.mem base (slot 5 + 8 * j)).toNat < Mb
    rw [v8 j hj]; exact Nat.lt_of_lt_of_le (VG.Proof.X448.AArch64.Base.limb_lt _ _) (by decide)
  -- `R`, doubled twice.
  rw [WP.seq_iff]
  refine WP.mono (Point56.doubleCall_ok hs8 b8 z8) fun t9 ⟨k9, b9, s9, _, _, m9, e9, _⟩ => ?_
  have hs9 := k9.scr hs8
  have one9 : EV t9.mem base 20 = 1 := by rw [Same.env s9 (i := 20) (by decide)]; exact one8
  rw [WP.seq_iff]
  refine WP.mono (Point56.doubleCall_ok hs9 b9 m9) fun t10 ⟨k10, b10, s10, _, _, _, e10, _⟩ => ?_
  have hs10 := k10.scr hs9
  have r10 : pt (EV t10.mem base) 3 4 5 = dbl2 ⟨FV s.mem base RX, FV s.mem base RY, 1⟩ := by
    rw [e10, dblEnv_345, one9, dblPt_eq, e9, dblEnv_345, one8, dblPt_eq, r8]; rfl
  have q10 : pt (EV t10.mem base) 0 1 2 = dbl2 (addPt (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 3 4 5)) := by
    rw [← q8]; simp only [pt]
    rw [Same.env s10 (i := 0) (by decide), Same.env s10 (i := 1) (by decide), Same.env s10 (i := 2) (by decide),
      Same.env s9 (i := 0) (by decide), Same.env s9 (i := 1) (by decide), Same.env s9 (i := 2) (by decide)]
  -- The products.
  refine block_codeOf ?_
  refine mulOp hs10 b10 12 0 5 (Or.inr (by decide)) fun t11 k11 b11 m12 s11 e11 => ?_
  have hs11 := k11.scr hs10
  refine mulOp hs11 b11 13 3 2 (Or.inr (by decide)) fun t12 k12 b12 m13 s12 e12 => ?_
  have hs12 := k12.scr hs11
  refine mulOp hs12 b12 14 1 5 (Or.inr (by decide)) fun t13 k13 b13 m14 s13 e13 => ?_
  have hs13 := k13.scr hs12
  refine mulOp hs13 b13 15 4 2 (Or.inr (by decide)) fun t k14 b14 m15 s14 e14 => WP.block_nil ?_
  have qx : EV t10.mem base 0 = (dbl2 (addPt (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 3 4 5))).X :=
    congrArg Point.X q10
  have qy : EV t10.mem base 1 = (dbl2 (addPt (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 3 4 5))).Y :=
    congrArg Point.Y q10
  have qz : EV t10.mem base 2 = (dbl2 (addPt (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 3 4 5))).Z :=
    congrArg Point.Z q10
  have rx : EV t10.mem base 3 = (dbl2 ⟨FV s.mem base RX, FV s.mem base RY, 1⟩).X := congrArg Point.X r10
  have ry : EV t10.mem base 4 = (dbl2 ⟨FV s.mem base RX, FV s.mem base RY, 1⟩).Y := congrArg Point.Y r10
  have rz : EV t10.mem base 5 = (dbl2 ⟨FV s.mem base RX, FV s.mem base RY, 1⟩).Z := congrArg Point.Z r10
  have kf : FKeep base t10 t := k11.trans (k12.trans (k13.trans k14))
  refine ⟨kf.scr hs10, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (((((((((crossClob_clob k1).trans (crossClob_ckeep k2)).trans (crossClob_ckeep k3)).trans
      (crossClob_ckeep k4)).trans (crossClob_clob k5)).trans (crossClob_clob k6)).trans (crossClob_clob k7)).trans
      (k8.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; decide))).trans
      ((crossClob_ckeep k9).trans (crossClob_ckeep k10))).trans
      (kf.regs.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hr)))
  · have o1' : Outside2 base 64 2816 ACC 1152 s.mem t1.mem := fun x a _ => f1 x (by simp only [slot] at a ⊢; omega)
    have o58 : Outside2 base 64 2816 ACC 1152 t4.mem t8.mem := fun x a _ => by
      rw [o8 x (by simp only [slot] at a ⊢; omega), o7 x (by simp only [slot] at a ⊢; omega),
        o6 x (by simp only [slot] at a ⊢; omega), f5 x (by simp only [slot] at a ⊢; omega)]
    exact ((((((o1'.trans k2.mem).trans k3.mem).trans k4.mem).trans o58).trans k9.mem).trans k10.mem).trans kf.mem
  · rw [Same.env s14 (i := 12) (by decide), Same.env s13 (i := 12) (by decide), Same.env s12 (i := 12) (by decide),
      e11, Function.update_self, qx, rz]
  · rw [Same.env s14 (i := 13) (by decide), Same.env s13 (i := 13) (by decide), e12, Function.update_self,
      Same.env s11 (i := 3) (by decide), Same.env s11 (i := 2) (by decide), rx, qz]
  · rw [Same.env s14 (i := 14) (by decide), e13, Function.update_self, Same.env s12 (i := 1) (by decide),
      Same.env s11 (i := 1) (by decide), Same.env s12 (i := 5) (by decide), Same.env s11 (i := 5) (by decide), qy, rz]
  · rw [e14, Function.update_self, Same.env s13 (i := 4) (by decide), Same.env s12 (i := 4) (by decide),
      Same.env s11 (i := 4) (by decide), Same.env s13 (i := 2) (by decide), Same.env s12 (i := 2) (by decide),
      Same.env s11 (i := 2) (by decide), ry, qz]
  · intro i h1 h2
    have hi : i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by
      rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at h1 h2 ⊢; omega
    rcases hi with rfl | rfl | rfl | rfl
    · exact s14.bnd (by decide) (s13.bnd (by decide) (s12.bnd (by decide) m12))
    · exact s14.bnd (by decide) (s13.bnd (by decide) m13)
    · exact s14.bnd (by decide) m14
    · exact m15

end VG.Proof.Ed448.AArch64.Window
