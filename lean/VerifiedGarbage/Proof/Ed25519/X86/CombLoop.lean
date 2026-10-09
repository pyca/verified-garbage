import VerifiedGarbage.Proof.Ed25519.X86.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86.PointMul
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Call

/-!
# The comb's loop

The mixed additions (`addOddOps`, `addEvenOps`) add an affine cached point
exactly as the specification's `pointAdd`; `combNeg` negates the selected
entry under its sign's mask; after step `j`, the accumulator `A` (slots 0–3)
represents `[G + Σ_{i < j} d_{2i+1} 256^i]B` and `B` (slots 17–20) represents
`[G + Σ_{i < j} d_{2i} 256^i]B` (`Proof/Ed25519/CombDigits.lean`); at the end,
`16 A + B` is the scalar's multiple.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86 (sc)

/-! ## Frames -/

theorem MulKeep.of_field {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : FieldKeep x s t) :
    MulKeep x s t := MulKeep.of_ikeep hc (IKeep.of_field h)

theorem MulKeep.of_call {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : CallKeep x s t) :
    MulKeep x s t := MulKeep.of_ikeep hc (IKeep.of_call h)

theorem MulKeep.of_digit {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : DigitKeep x s t) :
    MulKeep x s t := by
  refine ⟨h.keep.edi, h.keep.esp, h.keep.rd, h.keep.wr, h.frame.sub fun r hr => ?_⟩
  rw [List.mem_singleton.mp hr]
  exact ⟨sub x 24 7144, List.mem_cons_self .., sub_sub hc.fit (by omega) (by omega) (by omega)⟩

theorem MulKeep.of_sel {x : BitVec 32} {s t : State} (hc : Ctx x s) (k : Keep s t)
    (h : SelFrame x s.mem t.mem) : MulKeep x s t :=
  ⟨k.edi, k.esp, k.rd, k.wr, h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨sub x 24 7144, List.mem_cons_self .., ?_⟩
    rcases hr with rfl | rfl
    · exact sub_sub hc.fit (by decide) (by decide) (by decide)
    · exact sub_sub hc.fit (by decide) (by decide) (by decide)⟩

theorem MulKeep.of_keepMem {x : BitVec 32} {s t : State} (k : Keep s t) (h : t.mem = s.mem) :
    MulKeep x s t := ⟨k.edi, k.esp, k.rd, k.wr, by rw [h]; exact Frame.refl _ _⟩

/-- The tables survive the comb's writes, to the workspace and the stack a call uses. -/
theorem TblAt.mulkeep {x P : BitVec 32} {s t : State} (h : TblAt x P s) (hc : Ctx x s)
    (hstk : (TBL (P.setWidth 64)).Disjoint (callStk s)) (k : MulKeep x s t) : TblAt x P t := by
  have hl := combWords_length
  refine ⟨h.fit, k.rd ▸ h.rd, fun i hi => ?_, h.far⟩
  rw [← h.words i hi]
  refine k.frame.readW (r := TBL (P.setWidth 64)) (Offset.contains_base _ (by omega) (by omega))
    (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.far.sub_right (by rw [scR_eq]; exact sub_sub hc.fit (by decide) (by decide) (by decide))
  · exact hstk

/-! ## The mixed additions -/

/-- What `addOddOps` and `addEvenOps` compute, from the accumulator's coordinates and the cached
entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> grind

theorem addOdd_formula (e : Env) :
    point (evalOps addOddOps e) 0 1 2 3 = mixedResult (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) := rfl

theorem addEven_formula (e : Env) :
    point (evalOps addEvenOps e) 17 18 19 20 =
      mixedResult (e 17) (e 18) (e 19) (e 20) (e 13) (e 14) (e 15) := rfl

theorem mixed_eval {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point}
    (hq : cachedAt e a b c = cache q) (p : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (e a) (e b) (e c) = Spec.Ed25519.pointAdd p q := by
  have h4 : e a = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e b = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e c = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  rw [h4, h5, h6, mixedResult_eq p q hz]

theorem addOdd_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (q : Spec.Ed25519.Point) (hq : cachedAt (env s.mem x) 4 5 6 = cache q) (hz : q.Z = 1) :
    WP isa (.block (fieldCode addOddOps)) s fun t =>
      FieldKeep x s t ∧ point (env t.mem x) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem x) 0 1 2 3) q ∧
      ∀ i : Slot, (4 ≤ i.val ∧ i.val < 8 ∨ 13 ≤ i.val) → env t.mem x i = env s.mem x i := by
  refine WP.mono (fieldCode_ok addOddOps hc) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  refine ⟨hk, (addOdd_formula _).trans (mixed_eval hq (point (env s.mem x) 0 1 2 3) hz),
    fun i hi => ?_⟩
  apply evalOps_unchanged
  intro op hop h
  have : ∀ op ∈ addOddOps, (fieldDest op).val < 4 ∨ (8 ≤ (fieldDest op).val ∧ (fieldDest op).val < 13) :=
    by decide
  have := this op hop
  rw [← h] at this
  omega

theorem addEven_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (q : Spec.Ed25519.Point) (hq : cachedAt (env s.mem x) 13 14 15 = cache q) (hz : q.Z = 1) :
    WP isa (.block (fieldCode addEvenOps)) s fun t =>
      FieldKeep x s t ∧ point (env t.mem x) 17 18 19 20 =
        Spec.Ed25519.pointAdd (point (env s.mem x) 17 18 19 20) q ∧
      ∀ i : Slot, (i.val < 8 ∨ 13 ≤ i.val ∧ i.val < 17 ∨ 21 ≤ i.val) →
        env t.mem x i = env s.mem x i := by
  refine WP.mono (fieldCode_ok addEvenOps hc) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  refine ⟨hk, (addEven_formula _).trans (mixed_eval hq (point (env s.mem x) 17 18 19 20) hz),
    fun i hi => ?_⟩
  apply evalOps_unchanged
  intro op hop h
  have : ∀ op ∈ addEvenOps, (8 ≤ (fieldDest op).val ∧ (fieldDest op).val < 13) ∨
      (17 ≤ (fieldDest op).val ∧ (fieldDest op).val < 21) := by decide
  have := this op hop
  rw [← h] at this
  omega

/-! ## The negations -/

/-- The negation, on the environment. -/
theorem neg_env (e : Env) (a b c : Slot) (sw : Bool) (hab : a ≠ b) (hc8 : c ≠ 8) (ha : a ≠ 8)
    (hb : b ≠ 8) (hac : a ≠ c) (hbc : b ≠ c) (hz : e 21 = 0) :
    cachedAt (swapsEnv [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e)) a b c =
      if sw then negCached (cachedAt e a b c) else cachedAt e a b c := by
  cases sw <;> simp [cachedAt, negCached, swapsEnv, swapEnv, evalOps, evalOp,
    hab, hc8, ha, hb, ha.symm, hb.symm, hac, hac.symm, hbc, hbc.symm, hz]

theorem neg_other (e : Env) (a b c : Slot) (sw : Bool) (i : Slot) (ha : i ≠ a) (hb : i ≠ b)
    (hc : i ≠ c) (h8 : i ≠ 8) :
    swapsEnv [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e) i = e i := by
  cases sw <;> simp [swapsEnv, swapEnv, evalOps, evalOp, Function.update_apply, ha, hb, hc, h8]

theorem combNeg_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (a b c : Slot) {sign : Nat}
    (hs1 : 928 ≤ sign) (hs2 : sign + 4 ≤ 8192) (sw : Bool) (hm : wd s.mem x sign = mask sw.toNat)
    (hdis : ∀ p ∈ [(a, b), (c, (8 : Slot))], p.1 ≠ p.2) :
    WP isa (.block (combNeg a b c sign)) s fun t => FieldKeep x s t ∧
      env t.mem x = swapsEnv [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] (env s.mem x)) := by
  rw [combNeg, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.sub 8 21 c] hc) fun u ⟨ku, vu⟩ => ?_
  have cu := ku.ctx hc
  rw [List.singleton_append]
  refine Wp.wp_ldm cu.edi (cu.inRW hs2 (by decide)) fun v hv => ?_
  have kv : FieldKeep x u v := FieldKeep.of_mem (updKeep hv) hv.mem
  have hmv : v.gpr .ecx = mask sw.toNat := by
    rw [hv.gpr]
    change wd u.mem x sign = _
    rw [wd_frame1 ku.frame hc.fit (by decide) hs2 (Or.inr (by omega))]
    exact hm
  refine WP.mono (swapFields_ok (kv.ctx cu) _ hdis sw hmv) fun t ⟨kt, _, vt⟩ =>
    ⟨(ku.trans kv).trans kt, ?_⟩
  rw [vt, hv.mem, vu]

/-! ## Four doublings -/

structure Double4Inv (x : BitVec 32) (s₀ : State) (n : Nat) (s : State) : Prop where
  lo : 1 ≤ n
  hi : n ≤ 4
  keep : IKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : point (env s.mem x) 0 1 2 3 = powerPoint (point (env s₀.mem x) 0 1 2 3) (4 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem x i = env s₀.mem x i

theorem double4_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa double4 s fun t => IKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = powerPoint (point (env s.mem x) 0 1 2 3) 4 ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.seq (Wp.wp_movi fun t ht => WP.block_nil ?_)
  refine WP.loop (M := isa) (Inv := Double4Inv x s) ?_ 4 t
    ⟨by decide, by decide, IKeep.of_counter ht, ht.gpr, ?_, ?_⟩
  · intro n u h
    have du : env u.mem x 16 = Spec.Ed25519.d := (h.high 16 (by decide)).trans hd
    refine WP.mono (doubleBody_ok (h.keep.ctx hc) h.lo (by omega_using [h.hi]) h.counter du)
      fun v ⟨kv, bv, zv, pv, high⟩ => ?_
    have kk := h.keep.trans kv
    have pp : point (env v.mem x) 0 1 2 3 =
        powerPoint (point (env s.mem x) 0 1 2 3) (4 - (n - 1)) := by
      exact pv.trans ((congrArg₂ Spec.Ed25519.pointAdd h.value h.value).trans
        (by rw [show 4 - (n - 1) = (4 - n) + 1 by omega_using [h.lo, h.hi]]; rfl))
    have hh : ∀ i : Slot, 16 ≤ i.val → env v.mem x i = env s.mem x i :=
      fun i hi => (high i hi).trans (h.high i hi)
    by_cases hn : n = 1
    · subst n
      exact .inl ⟨by rw [zv]; rfl, kk, pp, hh⟩
    · exact .inr ⟨by rw [zv]; simp only [show n - 1 ≠ 0 by omega_using [hn, h.lo], decide_false]; rfl,
        n - 1, by omega_using [h.lo], by omega_using [hn, h.lo], by omega_using [h.hi], kk, bv, pp, hh⟩
  · rw [ht.mem]; rfl
  · rw [ht.mem]; exact fun _ _ => rfl

/-! ## The loop -/

theorem digit_env {x : BitVec 32} {m m' : Mem} (hf : Frame [sub x 1024 136] m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) : env m' x = env m x := by
  funext i
  have hi := i.isLt
  exact congrArg VG.Proof.X25519.toFe (fe_frame fun k hk =>
    wd_frame1 hf hx (by decide) (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)))

theorem sel_env {x : BitVec 32} {m m' : Mem} (hf : SelFrame x m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (i : Slot) (hi : i.val < 4 ∨ (7 ≤ i.val ∧ i.val < 13) ∨ 16 ≤ i.val) : env m' x i = env m x i := by
  have hl := i.isLt
  exact congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)
    · exact sub_disj (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega))

theorem combNext_ok {s : State} {j : Nat} (hj : j < 32) (h : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 32)]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (j + 1) ∧ isa.eval .ne t = some (!decide (j + 1 = 32)) ∧
      t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mem = s.mem := by
  refine Wp.wp_addi fun u hu => Wp.wp_cmpi fun t ht _ zt => WP.block_nil ?_
  have e : u.gpr .esi = BitVec.ofNat 32 (j + 1) := by rw [hu.gpr, h, BitVec.ofNat_add]; rfl
  refine ⟨by rw [ht.gpr, e], ?_, by rw [ht.gpr, hu.other .edi (by decide)],
    by rw [ht.gpr, hu.other .esp (by decide)], by rw [ht.rd, hu.rd], by rw [ht.wr, hu.wr],
    by rw [ht.mem, hu.mem]⟩
  show t.zf.map (!·) = _
  rw [zt, e, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Wp.sub_beq (by omega) (by omega)]
  rfl

/-- The loop's invariant, after `j` steps, with the tables' address `P`. -/
structure CombInv (x : BitVec 32) (s₀ : State) (S : Nat) (P : BitVec 32) (j : Nat) (s : State) :
    Prop where
  bound : j ≤ 32
  keep : MulKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 j
  ptr : wd s.mem x combTbl = P
  zero : env s.mem x 21 = 0
  d : env s.mem x 16 = Spec.Ed25519.d
  odd : Rep (point (env s.mem x) 0 1 2 3) ((combGVal + oddSumZ S j) • baseAff)
  even : Rep (point (env s.mem x) 17 18 19 20) ((combGVal + evenSumZ S j) • baseAff)

private theorem dis_odd : ∀ ab ∈ [((4 : Slot), (5 : Slot)), (6, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

private theorem dis_even : ∀ ab ∈ [((13 : Slot), (14 : Slot)), (15, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

theorem combStep_ok {x P : BitVec 32} {s₀ s : State} (hc₀ : Ctx x s₀) {S j : Nat}
    (hb : ∀ q < 256, s₀.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (ht₀ : TblAt x P s₀) (hts : (TBL (P.setWidth 64)).Disjoint (callStk s₀))
    (h : CombInv x s₀ S P j s) (hj : j < 32) :
    WP isa combStep s fun t => isa.eval .ne t = some (!decide (j + 1 = 32)) ∧
      CombInv x s₀ S P (j + 1) t := by
  have hc := h.keep.ctx hc₀
  have hfit := hc.fit
  have bits : ∀ q < 256, s.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) :=
    fun q hq => (h.keep.bit hc₀ q (by omega)).trans (hb q hq)
  rw [combStep]
  have no := nib_lt S (2 * j + 1)
  have ne := nib_lt S (2 * j)
  -- Both digits' masks.
  refine WP.seq (WP.mono (combDigits_ok hc hj h.counter bits) fun a ⟨ka, ma⟩ => ?_)
  have ca := ka.keep.ctx hc
  have ea : env a.mem x = env s.mem x := digit_env ka.frame hfit
  have pa : wd a.mem x combTbl = P :=
    (wd_frame1 ka.frame hfit (by decide) (by decide) (Or.inr (by decide))).trans h.ptr
  have ta : TblAt x P a := ht₀.mulkeep hc₀ hts (h.keep.trans (MulKeep.of_digit hc ka))
  -- Both entries.
  refine WP.seq (WP.mono (combSelect_ok ca (mag_lt no) (mag_lt ne) ⟨ma.oddMask, ma.evenMask⟩ hj
    (ka.keep.esi.trans h.counter) pa ta) fun b ⟨bo, be, kb, fb⟩ => ?_)
  have cb := kb.ctx ca
  have eb : ∀ i : Slot, (i.val < 4 ∨ (7 ≤ i.val ∧ i.val < 13) ∨ 16 ≤ i.val) →
      env b.mem x i = env s.mem x i := fun i hi => by rw [sel_env fb hfit i hi, ea]
  have sb : ∀ o, 1024 ≤ o → o + 4 ≤ 8192 → wd b.mem x o = wd a.mem x o := fun o h1 h2 =>
    wd_frame fb fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj (by omega) (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))
      · exact sub_disj (by omega) (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))
  -- The odd entry, negated for a negative digit, and added.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (combNeg_ok cb 4 5 6 (by decide) (by decide) (decide (nib S (2 * j + 1) < 8))
    (by rw [sb _ (by decide) (by decide)]; exact ma.oddSign) dis_odd) fun c ⟨kc, vc⟩ => ?_
  obtain ⟨qo, hqo, hqoz, hrqo⟩ := combEntry_ok j (nib S (2 * j + 1)) hj no
  have b21 : env b.mem x 21 = 0 := (eb 21 (by decide)).trans h.zero
  have co : cachedAt (env c.mem x) 4 5 6 = cache qo := by
    rw [vc, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      b21, bo, ← hqo]
    by_cases hlt : nib S (2 * j + 1) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  have ec : ∀ i : Slot, (i.val < 4 ∨ 9 ≤ i.val) → env c.mem x i = env b.mem x i := fun i hi => by
    rw [vc, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
  have cc := kc.ctx cb
  refine WP.mono (addOdd_ok cc qo co hqoz) fun d ⟨kd, dp, dh⟩ => ?_
  -- The even entry, negated for a negative digit, and added.
  have cd := kd.ctx cc
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have sd : wd d.mem x combEvenSign = wd b.mem x combEvenSign := by
    rw [wd_frame1 kd.frame hfit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 kc.frame hfit (by decide) (by decide) (Or.inr (by decide))]
  refine WP.mono (combNeg_ok cd 13 14 15 (by decide) (by decide) (decide (nib S (2 * j) < 8))
    (by rw [sd, sb _ (by decide) (by decide)]; exact ma.evenSign) dis_even) fun f ⟨kf, vf⟩ => ?_
  obtain ⟨qe, hqe, hqez, hrqe⟩ := combEntry_ok j (nib S (2 * j)) hj ne
  have ed : ∀ i : Slot, 13 ≤ i.val → env d.mem x i = env b.mem x i := fun i hi => by
    rw [dh i (Or.inr hi), ec i (Or.inr (by omega))]
  have fe' : cachedAt (env f.mem x) 13 14 15 = cache qe := by
    rw [vf, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ((ed 21 (by decide)).trans b21)]
    have : cachedAt (env d.mem x) 13 14 15 = cachedAt (env b.mem x) 13 14 15 := by
      simp only [cachedAt, ed 13 (by decide), ed 14 (by decide), ed 15 (by decide)]
    rw [this, be, ← hqe]
    by_cases hlt : nib S (2 * j) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  have ef : ∀ i : Slot, (i.val < 8 ∨ 16 ≤ i.val) → env f.mem x i = env d.mem x i := fun i hi => by
    rw [vf, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
  have cf := kf.ctx cd
  rw [WP.block_append_iff]
  refine WP.mono (addEven_ok cf qe fe' hqez) fun g ⟨kg, gp, gh⟩ => ?_
  have g19 : g.gpr .esi = BitVec.ofNat 32 j := by
    rw [kg.keep.esi, kf.keep.esi, kd.keep.esi, kc.keep.esi, kb.esi, ka.keep.esi, h.counter]
  refine WP.mono (combNext_ok hj g19) fun t ⟨t19, t8, tedi, tesp, trd, twr, tmem⟩ => ⟨t8, ?_⟩
  have kgt : MulKeep x g t := ⟨tedi, tesp, trd, twr, by rw [tmem]; exact Frame.refl _ _⟩
  have kst : MulKeep x s t := (((((((MulKeep.of_digit hc ka).trans (MulKeep.of_sel ca kb fb)).trans
    (MulKeep.of_field cb kc)).trans (MulKeep.of_field cc kd)).trans (MulKeep.of_field cd kf)).trans
    (MulKeep.of_field cf kg)).trans kgt)
  -- Slots 0–3 after the odd addition; 17–20 after the even one.
  have eg : ∀ i : Slot, i.val < 4 → env g.mem x i = env d.mem x i := fun i hi => by
    rw [gh i (Or.inl (by omega)), ef i (Or.inl (by omega))]
  have pc : point (env c.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
    simp only [point, ec 0 (by decide), ec 1 (by decide), ec 2 (by decide), ec 3 (by decide),
      eb 0 (by decide), eb 1 (by decide), eb 2 (by decide), eb 3 (by decide)]
  have pf : point (env f.mem x) 17 18 19 20 = point (env s.mem x) 17 18 19 20 := by
    simp only [point, ef 17 (by decide), ef 18 (by decide), ef 19 (by decide), ef 20 (by decide),
      ed 17 (by decide), ed 18 (by decide), ed 19 (by decide), ed 20 (by decide),
      eb 17 (by decide), eb 18 (by decide), eb 19 (by decide), eb 20 (by decide)]
  have pt : wd t.mem x combTbl = P := by
    rw [tmem, wd_frame1 kg.frame hfit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 kf.frame hfit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 kd.frame hfit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 kc.frame hfit (by decide) (by decide) (Or.inr (by decide)),
      sb _ (by decide) (by decide)]
    exact pa
  refine ⟨by omega, h.keep.trans kst, t19, pt, ?_, ?_, ?_, ?_⟩
  · rw [tmem, gh 21 (Or.inr (Or.inr (by decide))), ef 21 (by decide), ed 21 (by decide)]
    exact b21
  · rw [tmem, gh 16 (Or.inr (Or.inl (by decide))), ef 16 (by decide), ed 16 (by decide),
      eb 16 (by decide)]
    exact h.d
  · have pg : point (env g.mem x) 0 1 2 3 = point (env d.mem x) 0 1 2 3 := by
      simp only [point, eg 0 (by decide), eg 1 (by decide), eg 2 (by decide), eg 3 (by decide)]
    rw [tmem, pg, dp, pc, oddSumZ, ← add_assoc, add_smul]
    exact pointAdd_rep h.odd hrqo
  · rw [tmem, gp, pf, evenSumZ, ← add_assoc, add_smul]
    exact pointAdd_rep h.even hrqe

/-! ## The start and the end -/

theorem combInit_ok {s : State} {x : BitVec 32} (hc : Ctx x s) :
    WP isa (.block combInit) s fun t => MulKeep x s t ∧
      wd t.mem x combTbl = wd s.mem x combTbl ∧ env t.mem x 21 = 0 ∧
      env t.mem x 16 = env s.mem x 16 ∧
      point (env t.mem x) 0 1 2 3 = combG ∧ point (env t.mem x) 17 18 19 20 = combG ∧
      t.gpr .esi = BitVec.ofNat 32 0 := by
  rw [combInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hc) fun a ⟨ka, va⟩ => ?_
  refine Wp.wp_movi fun t ht => WP.block_nil ?_
  refine ⟨(MulKeep.of_field hc ka).trans ⟨ht.other .edi (by decide), ht.other .esp (by decide), ht.rd,
      ht.wr, by rw [ht.mem]; exact Frame.refl _ _⟩,
    by rw [ht.mem]; exact wd_frame1 ka.frame hc.fit (by decide) (by decide) (Or.inr (by decide)),
    ?_, ?_, ?_, ?_, ht.gpr⟩ <;> rw [ht.mem, va] <;> rfl

theorem combFinish_ok {s : State} {x : BitVec 32} (hc : Ctx x s) {v w : ℤ}
    (hd : env s.mem x 16 = Spec.Ed25519.d)
    (ha : Rep (point (env s.mem x) 0 1 2 3) (v • baseAff))
    (hb : Rep (point (env s.mem x) 17 18 19 20) (w • baseAff)) :
    WP isa combFinish s fun t =>
      Rep (point (env t.mem x) 0 1 2 3) ((16 * v + w) • baseAff) ∧ MulKeep x s t := by
  rw [combFinish]
  refine WP.seq (WP.mono (double4_ok hc hd) fun b ⟨kb, bp, bh⟩ => ?_)
  have cb := kb.ctx hc
  refine WP.seq (WP.mono (fieldCode_ok [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] cb)
    fun c ⟨kc, vc⟩ => ?_)
  have cc := kc.ctx cb
  have cd : env c.mem x 16 = Spec.Ed25519.d := by
    rw [vc, show evalOps [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] (env b.mem x) 16 =
      env b.mem x 16 from rfl, bh 16 (by decide), hd]
  refine WP.mono (pointAddCall_ok cc cd) fun t ⟨kt, tp, _⟩ => ?_
  refine ⟨?_, ((MulKeep.of_ikeep hc kb).trans (MulKeep.of_field cb kc)).trans (MulKeep.of_call cc kt)⟩
  have p0 : point (env c.mem x) 0 1 2 3 = point (env b.mem x) 0 1 2 3 := by rw [vc]; rfl
  have p4 : point (env c.mem x) 4 5 6 7 = point (env s.mem x) 17 18 19 20 := by
    rw [vc]
    show point (env b.mem x) 17 18 19 20 = _
    simp only [point, bh 17 (by decide), bh 18 (by decide), bh 19 (by decide), bh 20 (by decide)]
  rw [tp, p0, p4, bp, ← zsmul_16]
  have h4 := powerPoint_rep ha 4
  rw [show (2 ^ 4 : Nat) = 16 from rfl] at h4
  exact pointAdd_rep h4 hb

theorem combMultiply_ok {s : State} {x P : BitVec 32} (hc : Ctx x s) {S : Nat} (hS : S < 2 ^ 256)
    (hb : ∀ q < 256, s.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hd : env s.mem x 16 = Spec.Ed25519.d) (hp : wd s.mem x combTbl = P) (ht : TblAt x P s)
    (hts : (TBL (P.setWidth 64)).Disjoint (callStk s)) :
    WP isa combMultiply s fun t =>
      Rep (point (env t.mem x) 0 1 2 3) (S • baseAff) ∧ MulKeep x s t := by
  rw [combMultiply]
  refine WP.seq (WP.mono (combInit_ok hc) fun b ⟨kb, bt, bz, bd, bp, bq, b19⟩ => ?_)
  have hg : Rep combG (((combGVal : ℤ) + 0) • baseAff) := by
    rw [add_zero, natCast_zsmul]; exact combG_ok
  have init : CombInv x s S P 0 b :=
    ⟨by decide, kb, b19, bt.trans hp, bz, bd.trans hd, by rw [bp]; exact hg, by rw [bq]; exact hg⟩
  have hl : WP isa (.loop combStep .ne) b fun t => CombInv x s S P 32 t := by
    apply WP.loop (fun n t => CombInv x s S P (32 - n) t ∧ 0 < n ∧ n ≤ 32) (n := 32)
    · intro n t ⟨hi, hn0, hn⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      refine WP.mono (combStep_ok hc hb ht hts hi (by omega)) fun u ⟨u8, hu⟩ => ?_
      by_cases hk : k = 0
      · subst hk
        exact Or.inl ⟨by rw [u8]; rfl, hu⟩
      · refine Or.inr ⟨by rw [u8, show 32 - (k + 1) + 1 = 32 - k by omega,
          decide_eq_false (show 32 - k ≠ 32 by omega)]; rfl, k, by omega, ?_, by omega, by omega⟩
        rw [show 32 - k = 32 - (k + 1) + 1 by omega]; exact hu
    · exact ⟨init, by decide, by decide⟩
  refine WP.seq (WP.mono hl fun t hi => ?_)
  refine WP.mono (combFinish_ok (hi.keep.ctx hc) hi.d hi.odd hi.even) fun u ⟨hu, ku⟩ =>
    ⟨?_, hi.keep.trans ku⟩
  rw [comb_total hS, natCast_zsmul] at hu
  exact hu

end VG.Proof.Ed25519.X86
