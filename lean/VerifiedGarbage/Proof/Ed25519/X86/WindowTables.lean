import VerifiedGarbage.Proof.Ed25519.X86.VerifyTables
import VerifiedGarbage.Proof.Ed25519.X86.PointPowers
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Proof.Ed25519.Group.Double

/-!
# Verification's tables: `[1]A … [15]A` and `-[1]B … -[15]B`

The table of multiples of `A` (byte 1024) is built by repeated addition of `A`,
each entry representing its multiple (`Rep`); the table of negated multiples
of `B` (byte 3072) is stored from constants. Both hold points with the
specification's coordinates, added with `pointAdd`.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

/-! ## Frames -/

/-- A word outside the regions `[o, o + n)` and `[o', o' + n')` of the workspace. -/
theorem wd_frame2 {x : BitVec 32} {m m' : Mem} {o n o' n' d : Nat}
    (hf : Frame [sub x o n, sub x o' n'] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o + n ≤ 8192) (ho' : o' + n' ≤ 8192) (hd : d + 4 ≤ 8192)
    (h1 : d + 4 ≤ o ∨ o + n ≤ d) (h2 : d + 4 ≤ o' ∨ o' + n' ≤ d) : wd m' x d = wd m x d :=
  wd_frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega) (by omega) h1
    · exact sub_disj (by omega) (by omega) h2

theorem tablePoint_frame2 {x : BitVec 32} {m m' : Mem} {o n o' n' a : Nat}
    (hf : Frame [sub x o n, sub x o' n'] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o + n ≤ 8192) (ho' : o' + n' ≤ 8192) (ha : a + 128 ≤ 8192)
    (h1 : a + 128 ≤ o ∨ o + n ≤ a) (h2 : a + 128 ≤ o' ∨ o' + n' ≤ a) :
    tablePoint m' x a = tablePoint m x a :=
  table_point_of_words fun k hk => wd_frame2 hf hx ho ho' (by omega) (by omega) (by omega)

theorem env_frame2 {x : BitVec 32} {m m' : Mem} {o n o' n' : Nat}
    (hf : Frame [sub x o n, sub x o' n'] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o + n ≤ 8192) (ho' : o' + n' ≤ 8192) (i : Slot)
    (h1 : offset i + 32 ≤ o ∨ o + n ≤ offset i) (h2 : offset i + 32 ≤ o' ∨ o' + n' ≤ offset i) :
    env m' x i = env m x i := by
  have hi := i.isLt
  exact congrArg VG.Proof.X25519.toFe (fe_frame fun k hk =>
    wd_frame2 hf hx ho ho' (by simp only [offset] at h1 ⊢; omega) (by omega) (by omega))

/-- A frame of slots and of a region is one of slots and of a larger region. -/
theorem frame2_widen {x : BitVec 32} {m m' : Mem} {o n o' n' : Nat}
    (hf : Frame [sub x o n, sub x o' n'] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32) {p q p' q' : Nat}
    (h1 : p ≤ o) (h2 : o + n ≤ p + q) (h3 : p' ≤ o') (h4 : o' + n' ≤ p' + q') (h5 : o < 8192)
    (h6 : o' < 8192) : Frame [sub x p q, sub x p' q'] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_sub hx h1 h2 h5⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_sub hx h3 h4 h6⟩

/-- A frame of one region as one of two. -/
theorem frame1_two {x : BitVec 32} {m m' : Mem} {o n : Nat} (hf : Frame [sub x o n] m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) {p q p' q' : Nat} (h1 : p ≤ o) (h2 : o + n ≤ p + q) (h5 : o < 8192) :
    Frame [sub x p q, sub x p' q'] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_cons_self, sub_sub hx h1 h2 h5⟩

/-! Frames of two regions and the stack a call uses. -/

theorem wd_frame2s {x : BitVec 32} {s : State} (hc : Ctx x s) {m m' : Mem} {o n o' n' d : Nat}
    (hf : Frame [sub x o n, sub x o' n', callStk s] m m')
    (ho : o + n ≤ 8192) (ho' : o' + n' ≤ 8192) (hd : d + 4 ≤ 8192)
    (h1 : d + 4 ≤ o ∨ o + n ≤ d) (h2 : d + 4 ≤ o' ∨ o' + n' ≤ d) : wd m' x d = wd m x d := by
  have hx := hc.fit
  exact wd_frameS hc (rs := [sub x o n, sub x o' n']) hf hd fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega) (by omega) h1
    · exact sub_disj (by omega) (by omega) h2

theorem tablePoint_frame2s {x : BitVec 32} {s : State} (hc : Ctx x s) {m m' : Mem} {o n o' n' a : Nat}
    (hf : Frame [sub x o n, sub x o' n', callStk s] m m')
    (ho : o + n ≤ 8192) (ho' : o' + n' ≤ 8192) (ha : a + 128 ≤ 8192)
    (h1 : a + 128 ≤ o ∨ o + n ≤ a) (h2 : a + 128 ≤ o' ∨ o' + n' ≤ a) :
    tablePoint m' x a = tablePoint m x a :=
  table_point_of_words fun k hk => wd_frame2s hc hf ho ho' (by omega) (by omega) (by omega)

/-- A frame of two regions, and of a region and the stack, as one of both and the stack. -/
theorem Frame.two {x : BitVec 32} {s : State} {m m' : Mem} {o n o' n' : Nat}
    (hf : Frame [sub x o n, sub x o' n'] m m') : Frame [sub x o n, sub x o' n', callStk s] m m' :=
  hf.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp

theorem Frame.oneS {x : BitVec 32} {s : State} {m m' : Mem} {o n p q p' q' : Nat}
    (hf : Frame [sub x o n, callStk s] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32) (h1 : p ≤ o)
    (h2 : o + n ≤ p + q) (h5 : o < 8192) : Frame [sub x p q, sub x p' q', callStk s] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_sub hx h1 h2 h5⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem Frame.one' {x : BitVec 32} {s : State} {m m' : Mem} {o n p q p' q' : Nat}
    (hf : Frame [sub x o n] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32) (h1 : p' ≤ o)
    (h2 : o + n ≤ p' + q') (h5 : o < 8192) : Frame [sub x p q, sub x p' q', callStk s] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_sub hx h1 h2 h5⟩

/-- A frame of one region as the second of two. -/
theorem frame1_two' {x : BitVec 32} {m m' : Mem} {o n : Nat} (hf : Frame [sub x o n] m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) {p q p' q' : Nat} (h1 : p' ≤ o) (h2 : o + n ≤ p' + q') (h5 : o < 8192) :
    Frame [sub x p q, sub x p' q'] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_sub hx h1 h2 h5⟩

/-! ## Loading a table entry into slots 4–7 -/

theorem pointFromTableQ_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat}
    (hp : s.gpr .edx = x + BitVec.ofNat 32 o) (hlo : 320 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTableQ) s fun t =>
      IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧ point (env t.mem x) 4 5 6 7 = tablePoint s.mem x o ∧
      ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem x i = env s.mem x i := by
  have hb : s.gpr .edi = x + BitVec.ofNat 32 0 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hc.edi
  refine WP.mono (copyWorkspaceWords_ok hc .edx .edi (by decide) (by decide) o 0 0 192 32
    hp hb (by omega) (by decide) (Or.inr (by omega)) 32 (Nat.le_refl _)) fun t ⟨hk, hv⟩ => ?_
  have hf : Frame [sub x 192 128] s.mem t.mem := by simpa only [Nat.zero_add] using hk.frame
  refine ⟨⟨hk.gpr _ (by decide), hk.gpr _ (by decide), hk.rd, hk.wr,
    Frame.withStk (s := s) (frameWiden (n' := 960) hf hc.fit (by decide) (by decide) (by decide))⟩,
    hk.gpr _ (by decide), ?_, fun i hi => ?_⟩
  · have := table_point_of_words (m := s.mem) (m' := t.mem) (x := x) (a := o) (o := 192)
      (fun k hk' => by simpa only [Nat.zero_add, Nat.add_zero] using hv k hk')
    exact this
  · have hl := i.isLt
    exact congrArg VG.Proof.X25519.toFe (fe_frame1 hf hc.fit (by decide)
      (by simp only [offset]; omega) (by simp only [offset]; omega))

theorem pointTableQ_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o : Nat)
    (hlo : 320 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableQ o)) s fun t =>
      IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧ point (env t.mem x) 4 5 6 7 = tablePoint s.mem x o ∧
      ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem x i = env s.mem x i := by
  refine WP.block_append (WP.mono (tablePointer_ok hc o) fun a ⟨ka, ma, pa⟩ => ?_)
  refine WP.mono (pointFromTableQ_ok (ka.ctx hc) pa hlo hn) fun t ⟨kt, et, pt, ht⟩ => ?_
  exact ⟨(IKeep.of_mem ka ma).trans kt, et.trans ka.esi, by rw [pt, ma],
    fun i hi => by rw [ht i hi, ma]⟩

/-! ## `[i]A` -/

/-- The table of `A`'s multiples, with `n` entries and `[n]A` in slots 0–3. -/
structure ATableInv (x : BitVec 32) (s₀ : State) (A : Spec.Ed25519.Point) (Aa : EPoint dZ)
    (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 15
  ctx : Ctx x s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  d : env s.mem x 16 = Spec.Ed25519.d
  value : Rep (point (env s.mem x) 0 1 2 3) (n • Aa)
  table : ∀ j < n, Rep (tablePoint s.mem x (1024 + 128 * j)) ((j + 1) • Aa)
  a : tablePoint s.mem x 7680 = A
  keep : ScalarKeep s₀ s
  frame : Frame [sub x 64 960, sub x 1024 1920, callStk s₀] s₀.mem s.mem

theorem aTableInit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {A : Spec.Ed25519.Point}
    {Aa : EPoint dZ} (hA : Rep A Aa) (ha : tablePoint s.mem x 7680 = A)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (.block aTableInit) s (ATableInv x s A Aa 1) := by
  rw [aTableInit, List.append_assoc, WP.block_append_iff]
  refine WP.mono (pointTableRead_ok hc 7680 (by decide) (by decide)) fun a ⟨ka, pa, ha'⟩ => ?_
  have ca := ka.ctx hc
  rw [WP.block_append_iff]
  refine WP.mono (pointTableWrite_ok ca 1024 (by decide) (by decide)) fun b ⟨kb, fb, pb⟩ => ?_
  refine Wp.wp_movi fun t ht => WP.block_nil ?_
  have mt : t.mem = b.mem := ht.mem
  have eb : env b.mem x = env a.mem x := table_env hc.fit fb (by decide) (by decide)
  have fab : Frame [sub x 64 960, sub x 1024 1920, callStk s] s.mem t.mem := by
    rw [mt]
    exact (Frame.two (frame1_two ka.frame hc.fit (by decide) (by decide) (by decide))).trans
      (Frame.one' fb hc.fit (by decide) (by decide) (by decide))
  refine ⟨by decide, by decide, (ka.keep.ctx hc).keep (by rw [ht.other _ (by decide), kb.edi])
    (by rw [ht.wr, kb.wr]) (by rw [ht.other _ (by decide), kb.esp]), ht.gpr, ?_, ?_, ?_, ?_, ?_, fab⟩
  · rw [mt, eb, ha' 16 (by decide), hd]
  · rw [mt, eb, pa, ha, one_nsmul]; exact hA
  · intro j hj
    obtain rfl : j = 0 := by omega
    rw [mt, Nat.mul_zero, Nat.add_zero, pb, pa, ha, zero_add, one_nsmul]; exact hA
  · rw [tablePoint_frame2s hc fab (by decide) (by decide) (by decide) (Or.inr (by decide))
      (Or.inr (by decide))]
    exact ha
  · exact ⟨by rw [ht.other _ (by decide), kb.edi, ka.keep.edi], by rw [ht.other _ (by decide), kb.esp,
      ka.keep.esp], by rw [ht.rd, kb.rd, ka.keep.rd], by rw [ht.wr, kb.wr, ka.keep.wr]⟩

theorem esiNext_ok {s : State} {n m : Nat} (hn : n + 1 < 2 ^ 32) (hm : m < 2 ^ 32)
    (h : s.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (.block [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm (BitVec.ofNat 32 m))]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (n + 1) ∧ t.zf = some (decide (n + 1 = m)) ∧
      t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = s.mem := by
  refine Wp.wp_addi fun u hu => Wp.wp_cmpi fun t ht _ zt => WP.block_nil ?_
  have e : u.gpr .esi = BitVec.ofNat 32 (n + 1) := by rw [hu.gpr, h, BitVec.ofNat_add]; rfl
  refine ⟨by rw [ht.gpr, e], ?_, by rw [ht.gpr, hu.other .edi (by decide)],
    by rw [ht.gpr, hu.other .esp (by decide)], by rw [ht.rd, hu.rd], by rw [ht.wr, hu.wr],
    by rw [ht.mem, hu.mem]⟩
  rw [zt, e, Wp.sub_beq hn hm]

theorem aTableBody_ok {x : BitVec 32} {s₀ s : State} {A : Spec.Ed25519.Point} {Aa : EPoint dZ}
    {n : Nat} (hn : n < 15) (hA : Rep A Aa) (h : ATableInv x s₀ A Aa n s) :
    WP isa aTableBody s fun t => t.zf = some (decide (n + 1 = 15)) ∧
      ATableInv x s₀ A Aa (n + 1) t := by
  have hc := h.ctx
  have hfit := hc.fit
  have hs₀ : callStk s = callStk s₀ := by rw [callStk, callStk, h.keep.esp]
  unfold aTableBody
  refine WP.seq (WP.mono (pointTableQ_ok hc 7680 (by decide) (by decide)) fun a ⟨ka, ea, pa, ha⟩ => ?_)
  have ca := ka.ctx hc
  refine WP.seq (WP.mono (pointAdd_ok ca ((ha 16 (Or.inr (by decide))).trans h.d)) fun b ⟨kb, pb, hb⟩ => ?_)
  have cb := kb.ctx ca
  have kab : IKeep x s b := ka.trans (IKeep.of_call kb)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok cb 1024 n (by omega) (by rw [kb.keep.esi, ea, h.counter]))
    fun c ⟨kc, mc, pc⟩ => ?_
  have cc := kc.ctx cb
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok cc pc (by omega) (by omega)) fun d ⟨kd, pd⟩ => ?_
  refine WP.mono (esiNext_ok (m := 15) (by omega) (by decide)
    (by rw [kd.gpr _ (by decide), kc.esi, kb.keep.esi, ea, h.counter])) fun t ⟨te, tz, tedi, tesp, trd, twr, tm⟩ =>
      ⟨tz, ?_⟩
  have fab : Frame [sub x 64 960, sub x 1024 1920, callStk s] s.mem c.mem := by
    rw [mc]; exact Frame.oneS kab.frame hfit (by decide) (by decide) (by decide)
  have fd : Frame [sub x 64 960, sub x 1024 1920, callStk s] c.mem d.mem :=
    Frame.one' kd.frame hfit (by omega) (by omega) (by omega)
  have fall : Frame [sub x 64 960, sub x 1024 1920, callStk s₀] s.mem t.mem := by
    rw [tm, ← hs₀]; exact fab.trans fd
  have crep : Rep (point (env c.mem x) 0 1 2 3) ((n + 1) • Aa) := by
    rw [mc, pb, pa, h.a, succ_nsmul]
    have : point (env a.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
      simp only [point, ha 0 (Or.inl (by decide)), ha 1 (Or.inl (by decide)), ha 2 (Or.inl (by decide)),
        ha 3 (Or.inl (by decide))]
    rw [this]
    exact pointAdd_rep h.value hA
  have tpb : ∀ o, o + 128 ≤ 8192 → 1024 ≤ o → tablePoint b.mem x o = tablePoint s.mem x o := fun o h1 h2 =>
    table_point_of_words fun k hk => wd_frame1s hc kab.frame (by decide) (by omega) (Or.inr (by omega))
  refine ⟨by omega, by omega, ?_, te, ?_, ?_, fun j hj => ?_, ?_, ?_, h.frame.trans fall⟩
  · exact hc.keep (by rw [tedi, kd.gpr _ (by decide), kc.edi, kb.keep.edi, ka.edi])
      (by rw [twr, kd.wr, kc.wr, kb.keep.wr, ka.wr]) (by rw [tesp, kd.gpr _ (by decide), kc.esp, kb.keep.esp, ka.esp])
  · rw [tm, table_env hfit kd.frame (by omega) (by omega), mc, hb 16 (by decide),
      ha 16 (Or.inr (by decide))]
    exact h.d
  · rw [tm, table_env hfit kd.frame (by omega) (by omega)]; exact crep
  · rw [tm]
    by_cases hjn : j < n
    · rw [tablePoint_frame hfit kd.frame (by omega) (by omega) (Or.inl (by omega)), mc,
        tpb _ (by omega) (by omega)]
      exact h.table j hjn
    · obtain rfl : j = n := by omega
      rw [pd]; exact crep
  · rw [tm, tablePoint_frame hfit kd.frame (by omega) (by omega) (Or.inr (by omega)), mc,
      tpb _ (by decide) (by decide)]
    exact h.a
  · exact ⟨by rw [tedi, kd.gpr _ (by decide), kc.edi, kb.keep.edi, ka.edi, h.keep.edi],
      by rw [tesp, kd.gpr _ (by decide), kc.esp, kb.keep.esp, ka.esp, h.keep.esp],
      by rw [trd, kd.rd, kc.rd, kb.keep.rd, ka.rd, h.keep.rd],
      by rw [twr, kd.wr, kc.wr, kb.keep.wr, ka.wr, h.keep.wr]⟩

theorem aTable_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {A : Spec.Ed25519.Point}
    {Aa : EPoint dZ} (hA : Rep A Aa) (ha : tablePoint s.mem x 7680 = A)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa aTable s (ATableInv x s A Aa 15) := by
  refine WP.seq (WP.mono (aTableInit_ok hc hA ha hd) fun b (hb : ATableInv x s A Aa (15 - 14) b) => ?_)
  refine WP.loop (M := isa) (Inv := fun m t => ATableInv x s A Aa (15 - m) t ∧ 0 < m ∧ m ≤ 14) ?_ 14 b
    ⟨hb, by decide, by decide⟩
  intro m u ⟨hu, hm0, hm⟩
  refine WP.mono (aTableBody_ok (n := 15 - m) (by omega) hA hu) fun v ⟨zv, hv⟩ => ?_
  by_cases h1 : m = 1
  · subst m
    exact .inl ⟨by show v.zf.map (!·) = _; rw [zv]; rfl, hv⟩
  · refine .inr ⟨by show v.zf.map (!·) = _; rw [zv, decide_eq_false (by omega)]; rfl, m - 1, by omega,
      ?_, by omega, by omega⟩
    rw [show 15 - (m - 1) = 15 - m + 1 by omega]; exact hv

/-! ## `-[i]B` -/

theorem negBase_rep (i : Nat) (hi : i < 15) : Rep (negBase i) ((i + 1) • (-baseAff)) := by
  rw [smul_neg]; exact (baseMultiple_rep i hi).neg

theorem bEntry_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (i : Nat) (hi : i < 15) :
    WP isa (.block (bEntry i)) s fun t => ScalarKeep s t ∧
      Frame [sub x 64 864, sub x (3072 + 128 * i) 128] s.mem t.mem ∧
      tablePoint t.mem x (3072 + 128 * i) = negBase i ∧ env t.mem x 16 = env s.mem x 16 := by
  rw [bEntry, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hc) fun a ⟨ka, ea⟩ => ?_
  refine WP.mono (pointTableWrite_ok (ka.ctx hc) (3072 + 128 * i) (by omega) (by omega))
    fun t ⟨kt, ft, pt⟩ => ⟨(Keep.scalar ka.keep).trans kt, ?_, ?_, ?_⟩
  · exact (frame1_two ka.frame hc.fit (by decide) (by decide) (by decide)).trans
      (frame1_two' ft hc.fit (by omega) (by omega) (by omega))
  · rw [pt, ea, constPoint_eval]
  · rw [table_env hc.fit ft (by omega) (by omega), ea]; rfl

theorem bEntries_ok {x : BitVec 32} (l : List Nat) (hl : ∀ i ∈ l, i < 15) (hnd : l.Nodup) :
    ∀ {s : State}, Ctx x s → WP isa (bEntries l) s fun t => ScalarKeep s t ∧
      Frame [sub x 64 864, sub x 3072 1920] s.mem t.mem ∧
      (∀ i ∈ l, tablePoint t.mem x (3072 + 128 * i) = negBase i) ∧
      (∀ j < 15, j ∉ l → tablePoint t.mem x (3072 + 128 * j) = tablePoint s.mem x (3072 + 128 * j)) ∧
      env t.mem x 16 = env s.mem x 16 := by
  induction l with
  | nil => exact fun _ => WP.block_nil ⟨ScalarKeep.refl _, Frame.refl _ _, fun _ h => absurd h List.not_mem_nil,
      fun _ _ _ => rfl, rfl⟩
  | cons i is ih =>
    intro s hc
    have hi := hl i List.mem_cons_self
    have hnd' := List.nodup_cons.mp hnd
    rw [bEntries]
    refine WP.seq (WP.mono (bEntry_ok hc i hi) fun a ⟨ka, fa, pa, da⟩ => ?_)
    have ca : Ctx x a := hc.keep ka.edi ka.wr ka.esp
    refine WP.mono (ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) hnd'.2 ca)
      fun t ⟨kt, ft, et, ot, dt⟩ => ⟨ka.trans kt, ?_, fun j hj => ?_, fun j hj hjn => ?_, dt.trans da⟩
    · exact (frame2_widen fa hc.fit (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega) (by decide)
        (by omega)).trans ft
    · rcases List.mem_cons.mp hj with rfl | hj
      · rw [ot j hi hnd'.1, pa]
      · exact et j hj
    · rw [ot j hj (fun h => hjn (List.mem_cons_of_mem _ h)),
        tablePoint_frame2 fa hc.fit (by decide) (by omega) (by omega) (Or.inr (by omega))
          (by have : j ≠ i := fun e => hjn (e ▸ List.mem_cons_self); omega)]

theorem bTable_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa bTable s fun t => ScalarKeep s t ∧ Frame [sub x 64 864, sub x 3072 1920] s.mem t.mem ∧
      (∀ i < 15, Rep (tablePoint t.mem x (3072 + 128 * i)) ((i + 1) • (-baseAff))) ∧
      env t.mem x 16 = env s.mem x 16 := by
  refine WP.mono (bEntries_ok (List.range 15) (fun i hi => List.mem_range.mp hi) List.nodup_range hc)
    fun t ⟨kt, ft, et, _, dt⟩ => ⟨kt, ft, fun i hi => ?_, dt⟩
  rw [et i (List.mem_range.mpr hi)]; exact negBase_rep i hi

end VG.Proof.Ed25519.X86
