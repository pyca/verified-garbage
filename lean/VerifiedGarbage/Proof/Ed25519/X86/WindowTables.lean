module

import VerifiedGarbage.Proof.Ed25519.X86.VerifyTables
import VerifiedGarbage.Proof.Ed25519.X86.PointPowers
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Call
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyTbl
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ed25519.X86.PointTable
public import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
import VerifiedGarbage.Proof.Framework.X86.SymFrame

/-!
# Verification's tables: `[1]A … [15]A` and `-[1]B … -[15]B`

The table of multiples of `A` (byte 1024) is built by repeated addition of `A`,
each entry representing its multiple (`Rep`); the table of negated multiples
of `B` (byte 3072) is copied from the static `bSym`. Both hold points with the
specification's coordinates, added with `pointAdd`.
-/

@[expose] public section

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
  refine WP.seq (WP.mono (pointAddCall_ok ca ((ha 16 (Or.inr (by decide))).trans h.d)) fun b ⟨kb, pb, hb⟩ => ?_)
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

/-- A table entry whose dwords are the static's: `-[i + 1]B`. -/
theorem tablePoint_of_dwords {m : Mem} {x : BitVec 32} {i : Nat}
    (h : ∀ k < 32, wd m x (3072 + 4 * (32 * i + k)) = bDword (32 * i + k)) :
    tablePoint m x (3072 + 128 * i) = negBase i := by
  have hc : ∀ c < 4, F m x (3072 + 128 * i + 32 * c) = pointCoord (negBase i) c := fun c hc => by
    have he : fe m x (3072 + 128 * i + 32 * c) = (pointCoord (negBase i) c).val := by
      unfold fe
      rw [num_congr (g := fun k => (pointCoord (negBase i) c).val / (2 ^ 32) ^ k % 2 ^ 32) (fun k hk => by
        rw [wv, show 3072 + 128 * i + 32 * c + 4 * k = 3072 + 4 * (32 * i + (8 * c + k)) by omega,
          h _ (by omega), bDword, BitVec.toNat_ofNat, show (32 * i + (8 * c + k)) / 32 = i by omega,
          show (32 * i + (8 * c + k)) / 8 % 4 = c by omega, show (32 * i + (8 * c + k)) % 8 = k by omega]),
        num_digits]
      exact Nat.mod_eq_of_lt (by have h := (pointCoord (negBase i) c).isLt; simp only [Spec.X25519.P] at h; omega)
    rw [F, he, VG.Proof.X25519.toFe_self]
  have h0 := hc 0 (by decide)
  have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide)
  have h3 := hc 3 (by decide)
  rw [show 3072 + 128 * i + 32 * 0 = 3072 + 128 * i by omega] at h0
  rw [show 3072 + 128 * i + 32 * 1 = 3072 + 128 * i + 32 by omega] at h1
  rw [show 3072 + 128 * i + 32 * 2 = 3072 + 128 * i + 64 by omega] at h2
  rw [show 3072 + 128 * i + 32 * 3 = 3072 + 128 * i + 96 by omega] at h3
  rw [tablePoint, h0, h1, h2, h3]
  generalize negBase i = q
  rfl

/-- A word of the working space outside the table at byte 3072, through a frame of the table and
the stack a call uses. -/
theorem wd_frameT {x : BitVec 32} {s : State} (hc : Ctx x s) {m m' : Mem}
    (hf : Frame [sub x 3072 1920, callStk s] m m') {d : Nat} (hd : d + 4 ≤ 3072) :
    wd m' x d = wd m x d := by
  have hfit := hc.fit
  refine wd_frame hf fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_disj (by omega) (by omega) (Or.inl hd)
  · exact (hc.stk rfl (by decide)).2.sub_left (by rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega) (by omega))

theorem bTable_ok {x T : BitVec 32} {s : State} (hc : Ctx x s) (hT : BTblAt s x T) (hsym : s.syms bSym = T)
    (hstk : (⟨T.setWidth 64, 1920⟩ : Region).Disjoint (callStk s)) :
    WP isa bTable s fun t => ScalarKeep s t ∧ Frame [sub x 3072 1920, callStk s] s.mem t.mem ∧
      (∀ i < 15, Rep (tablePoint t.mem x (3072 + 128 * i)) ((i + 1) • (-baseAff))) ∧
      env t.mem x 16 = env s.mem x 16 ∧ t.syms = s.syms := by
  have hfit := hc.fit
  have hsp := (hc.stk rfl (by decide)).1
  have hTf := hT.fit
  -- The static, apart from what the copy writes.
  have hTd : ∀ r ∈ [sub x 3072 1920, callStk s], (⟨T.setWidth 64, 1920⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hT.sc.sub_right (by rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega) (by omega))
    · exact hstk
  -- After `n` dwords.
  let LI : Nat → State → Prop := fun n t => ScalarKeep s t ∧ t.syms = s.syms ∧
    t.gpr .esi = T + BitVec.ofNat 32 (4 * n) ∧ t.gpr .edx = x + BitVec.ofNat 32 (3072 + 4 * n) ∧
    t.gpr .ecx = BitVec.ofNat 32 (480 - n) ∧ Frame [sub x 3072 1920, callStk s] s.mem t.mem ∧
    ∀ k < n, wd t.mem x (3072 + 4 * k) = bDword k
  unfold bTable
  refine WP.seq (WP.mono (symFrame_ok bSym s (by omega)) fun s₁ h₁ => ?_)
  refine WP.seq (Wp.wp_mov fun u₁ v₁ => Wp.wp_mov fun u₂ v₂ => Wp.wp_addi fun u₃ v₃ =>
    Wp.wp_movi fun u₄ v₄ => WP.block_nil ?_)
  have k₄ : ScalarKeep s u₄ :=
    ⟨by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
        h₁.gpr _ (by decide)],
      by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
        h₁.gpr _ (by decide)],
      by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, h₁.rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, h₁.wr]⟩
  have i₀ : LI 0 u₄ := by
    refine ⟨k₄, by rw [v₄.syms, v₃.syms, v₂.syms, v₁.syms, h₁.syms], ?_, ?_, by rw [v₄.gpr]; rfl, ?_,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, h₁.addr, hsym]
      exact (BitVec.add_zero _).symm
    · rw [v₄.other _ (by decide), v₃.gpr, v₂.gpr, v₁.other _ (by decide), h₁.gpr _ (by decide), hc.edi]
      rfl
    · rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
      exact h₁.frame.sub fun r hr => ⟨callStk s, by simp, by
        rw [List.mem_singleton.mp hr]; exact below_sub (by decide) hsp⟩
  refine WP.mono (WP.loop (M := isa) (Q := LI 480) (fun m t => ∃ n, m = 480 - n ∧ n < 480 ∧ LI n t) ?_ 480 u₄
    ⟨0, rfl, by decide, i₀⟩) fun t ⟨kt, st, _, _, _, ft, bt⟩ => ⟨kt, ft, fun i hi => ?_, ?_, st⟩
  · rintro m t ⟨n, rfl, hn, kt, st, si, di, ci, ft, bt⟩
    have ct : Ctx x t := hc.keep kt.edi kt.wr kt.esp
    have Tt : BTblAt t x T := hT.of_frame ft hTd (by rw [kt.rd, kt.wr])
    refine Wp.wp_ldm (B := T + BitVec.ofNat 32 (4 * n)) (o := 0) si
      (by rw [show addr (T + BitVec.ofNat 32 (4 * n)) 0 = addr T (4 * n) by
            rw [addr_zero]; rfl]
          exact Tt.inR hn) fun u₁ w₁ => ?_
    refine Wp.wp_stm (B := x + BitVec.ofNat 32 (3072 + 4 * n)) (o := 0) (by rw [w₁.other _ (by decide), di])
      (by rw [show addr (x + BitVec.ofNat 32 (3072 + 4 * n)) 0 = addr x (3072 + 4 * n) by
            rw [addr_zero]; rfl]
          rw [w₁.wr]; exact ct.inW (by omega) (by decide)) fun u₂ w₂ => ?_
    refine Wp.wp_addi fun u₃ w₃ => Wp.wp_addi fun u₄ w₄ => Wp.wp_subi fun u₅ w₅ _ z₅ => WP.block_nil ?_
    have ea : addr (x + BitVec.ofNat 32 (3072 + 4 * n)) 0 = addr x (3072 + 4 * n) := by
      rw [addr_zero]; rfl
    have ev : u₁.gpr .eax = bDword n := by
      rw [w₁.gpr, show addr (T + BitVec.ofNat 32 (4 * n)) 0 = addr T (4 * n) by
        rw [addr_zero]; rfl]
      exact Tt.val n hn
    have m₅ : u₅.mem = t.mem.writeW (addr x (3072 + 4 * n)) (bDword n) := by
      rw [w₅.mem, w₄.mem, w₃.mem, w₂.mem, ea, ev, w₁.mem]
    have next : LI (n + 1) u₅ := by
      refine ⟨kt.trans ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
      · rw [w₅.other _ (by decide), w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide)]
      · rw [w₅.other _ (by decide), w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide)]
      · rw [w₅.rd, w₄.rd, w₃.rd, w₂.rd, w₁.rd]
      · rw [w₅.wr, w₄.wr, w₃.wr, w₂.wr, w₁.wr]
      · rw [w₅.syms, w₄.syms, w₃.syms, w₂.syms, w₁.syms, st]
      · rw [w₅.other _ (by decide), w₄.other _ (by decide), w₃.gpr, w₂.gpr, w₁.other _ (by decide), si,
          show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 4 * n + 4 = 4 * (n + 1) by omega]
      · rw [w₅.other _ (by decide), w₄.gpr, w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide), di,
          show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 3072 + 4 * n + 4 = 3072 + 4 * (n + 1) by omega]
      · rw [w₅.gpr, w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide), ci,
          Wp.ofNat_pred (by omega)]
        congr 1
      · rw [m₅]
        exact ft.writeW (List.mem_cons_self) _ (sub_contains (by omega) (by omega) (by omega) (by decide))
      · rw [m₅]
        by_cases e : k = n
        · subst e; exact wd_write_self _ _ _ _
        · rw [wd_write_ne _ _ (by omega) (by omega) (by omega)]
          exact bt k (by omega)
    have z : u₅.zf = some (decide (480 - (n + 1) = 0)) := by
      rw [z₅, w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide), ci,
        Wp.ofNat_pred (by omega), Wp.ofNat_beq_zero (by omega)]
      rfl
    by_cases done : n + 1 = 480
    · refine .inl ⟨?_, done ▸ next⟩
      simp only [eval, z, show 480 - (n + 1) = 0 by omega, decide_true, Option.map_some, Bool.not_true]
    · refine .inr ⟨?_, 480 - (n + 1), by omega, n + 1, rfl, by omega, next⟩
      simp only [eval, z, show 480 - (n + 1) ≠ 0 by omega, decide_false, Option.map_some, Bool.not_false]
  · rw [tablePoint_of_dwords fun k hk => bt _ (by omega)]
    exact negBase_rep i hi
  · show F t.mem x (offset 16) = F s.mem x (offset 16)
    refine congrArg VG.Proof.X25519.toFe (num_congr fun k hk => ?_)
    show (wd t.mem x (offset 16 + 4 * k)).toNat = (wd s.mem x (offset 16 + 4 * k)).toNat
    rw [wd_frameT hc ft (by simp only [offset]; omega)]

end VG.Proof.Ed25519.X86
