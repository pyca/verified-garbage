module

public import VerifiedGarbage.Proof.Ed25519.X86.VerifyContract
public import VerifiedGarbage.Proof.Ed25519.WindowNibble
public import VerifiedGarbage.Proof.Ed25519.DblPoint
public import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
public import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Call
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.Group.Double
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ed25519.X86.Points
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Ed25519.X86.CommonContract
public import VerifiedGarbage.Impl.Ed25519.X86.VerifyWindow
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ed25519.WindowConstants
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! ### `Ed25519.X86.WindowTables`, which this module and modules that import it used -/

section

/-! ### `Ed25519.X86.VerifyTables`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem tablePointer_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o : Nat) :
    WP isa (.block [.mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 o))]) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 o := by
  refine Wp.wp_mov fun a ha => Wp.wp_addi fun t ht => WP.block_nil ?_
  exact ⟨(updKeep ha).trans (updKeep ht), ht.mem.trans ha.mem, by rw [ht.gpr, ha.gpr, hc.edi]⟩

theorem pointTableWrite_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o : Nat)
    (ho : 192 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => ScalarKeep s t ∧ Frame [sub x o 128] s.mem t.mem ∧
      tablePoint t.mem x o = point (env s.mem x) 0 1 2 3 := by
  refine WP.block_append (WP.mono (tablePointer_ok hc o) fun a ⟨ka, ma, pa⟩ => ?_)
  refine WP.mono (pointToTable_ok (ka.ctx hc) pa ho hn) fun t ⟨kt, vt⟩ => ?_
  exact ⟨(Keep.scalar ka).trans ⟨kt.gpr _ (by decide), kt.gpr _ (by decide), kt.rd, kt.wr⟩,
    by rw [← ma]; exact kt.frame, by rw [ma] at vt; exact vt⟩

theorem pointTableRead_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o : Nat)
    (ho : 192 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = tablePoint s.mem x o ∧
      (∀ i : Slot, 4 ≤ i.val → env t.mem x i = env s.mem x i) := by
  refine WP.block_append (WP.mono (tablePointer_ok hc o) fun a ⟨ka, ma, pa⟩ => ?_)
  refine WP.mono (pointFromTable_ok (ka.ctx hc) pa ho hn) fun t ⟨kt, vt⟩ => ?_
  exact ⟨(FieldKeep.of_mem ka ma).trans (FieldKeep.of_copy kt (ka.ctx hc)),
    by rw [ma] at vt; exact vt, fun i hi => by rw [kt.high (ka.ctx hc) i hi, ma]⟩

end VG.Proof.Ed25519.X86

end

end


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
    · exact sub_disj (by omega_arith) (by omega_arith) h1
    · exact sub_disj (by omega_arith) (by omega_arith) h2

theorem tablePoint_frame2s {x : BitVec 32} {s : State} (hc : Ctx x s) {m m' : Mem} {o n o' n' a : Nat}
    (hf : Frame [sub x o n, sub x o' n', callStk s] m m')
    (ho : o + n ≤ 8192) (ho' : o' + n' ≤ 8192) (ha : a + 128 ≤ 8192)
    (h1 : a + 128 ≤ o ∨ o + n ≤ a) (h2 : a + 128 ≤ o' ∨ o' + n' ≤ a) :
    tablePoint m' x a = tablePoint m x a :=
  table_point_of_words fun k hk => wd_frame2s hc hf ho ho' (by omega_arith) (by omega_arith) (by omega_arith)

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

/-! ## Loading a table entry into slots 4–7 -/

theorem pointFromTableQ_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat}
    (hp : s.gpr .edx = x + BitVec.ofNat 32 o) (hlo : 320 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTableQ) s fun t =>
      IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧ point (env t.mem x) 4 5 6 7 = tablePoint s.mem x o ∧
      ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem x i = env s.mem x i := by
  obtain hb : s.gpr .edi = x + BitVec.ofNat 32 0 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hc.edi
  refine WP.mono (copyWorkspaceWords_ok hc .edx .edi (by decide) (by decide) o 0 0 192 32
    hp hb (by omega_arith) (by decide) (Or.inr (by omega_arith)) 32 (Nat.le_refl _)) fun t ⟨hk, hv⟩ => ?_
  obtain hf : Frame [sub x 192 128] s.mem t.mem := by simpa only [Nat.zero_add] using hk.frame
  refine ⟨⟨hk.gpr _ (by decide), hk.gpr _ (by decide), hk.rd, hk.wr,
    Frame.withStk (s := s) (frameWiden (n' := 960) hf hc.fit (by decide) (by decide) (by decide))⟩,
    hk.gpr _ (by decide), ?_, fun i hi => ?_⟩
  · have := table_point_of_words (m := s.mem) (m' := t.mem) (x := x) (a := o) (o := 192)
      (fun k hk' => by simpa only [Nat.zero_add, Nat.add_zero] using hv k hk')
    exact this
  · have hl := i.isLt
    exact congrArg VG.Proof.X25519.toFe (fe_frame1 hf hc.fit (by decide)
      (by simp only [offset]; omega_arith) (by simp only [offset]; omega_arith))

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
  obtain ca := ka.ctx hc
  rw [WP.block_append_iff]
  refine WP.mono (pointTableWrite_ok ca 1024 (by decide) (by decide)) fun b ⟨kb, fb, pb⟩ => ?_
  refine Wp.wp_movi fun t ht => WP.block_nil ?_
  have mt : t.mem = b.mem := ht.mem
  obtain eb : env b.mem x = env a.mem x := table_env hc.fit fb (by decide) (by decide)
  obtain fab : Frame [sub x 64 960, sub x 1024 1920, callStk s] s.mem t.mem := by
    rw [mt]
    exact (Frame.two (frame1_two ka.frame hc.fit (by decide) (by decide) (by decide))).trans
      (Frame.one' fb hc.fit (by decide) (by decide) (by decide))
  refine ⟨by decide, by decide, (ka.keep.ctx hc).keep (by rw [ht.other _ (by decide), kb.edi])
    (by rw [ht.wr, kb.wr]) (by rw [ht.other _ (by decide), kb.esp]), ht.gpr, ?_, ?_, ?_, ?_, ?_, fab⟩
  · rw [mt, eb, ha' 16 (by decide), hd]
  · rw [mt, eb, pa, ha, one_nsmul]; exact hA
  · intro j hj
    obtain rfl : j = 0 := by omega_arith
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
  obtain e : u.gpr .esi = BitVec.ofNat 32 (n + 1) := by rw [hu.gpr, h, BitVec.ofNat_add]; rfl
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
  obtain hs₀ : callStk s = callStk s₀ := by rw [callStk, callStk, h.keep.esp]
  unfold aTableBody
  refine WP.seq (WP.mono (pointTableQ_ok hc 7680 (by decide) (by decide)) fun a ⟨ka, ea, pa, ha⟩ => ?_)
  obtain ca := ka.ctx hc
  refine WP.seq (WP.mono (pointAddCall_ok ca ((ha 16 (Or.inr (by decide))).trans h.d)) fun b ⟨kb, pb, hb⟩ => ?_)
  obtain cb := kb.ctx ca
  obtain kab : IKeep x s b := ka.trans (IKeep.of_call kb)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok cb 1024 n (by omega_arith) (by rw [kb.keep.esi, ea, h.counter]))
    fun c ⟨kc, mc, pc⟩ => ?_
  obtain cc := kc.ctx cb
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok cc pc (by omega_arith) (by omega_arith)) fun d ⟨kd, pd⟩ => ?_
  refine WP.mono (esiNext_ok (m := 15) (by omega_arith) (by decide)
    (by rw [kd.gpr _ (by decide), kc.esi, kb.keep.esi, ea, h.counter])) fun t ⟨te, tz, tedi, tesp, trd, twr, tm⟩ =>
      ⟨tz, ?_⟩
  obtain fab : Frame [sub x 64 960, sub x 1024 1920, callStk s] s.mem c.mem := by
    rw [mc]; exact Frame.oneS kab.frame hfit (by decide) (by decide) (by decide)
  obtain fd : Frame [sub x 64 960, sub x 1024 1920, callStk s] c.mem d.mem :=
    Frame.one' kd.frame hfit (by omega_arith) (by omega_arith) (by omega_arith)
  obtain fall : Frame [sub x 64 960, sub x 1024 1920, callStk s₀] s.mem t.mem := by
    rw [tm, ← hs₀]; exact fab.trans fd
  obtain crep : Rep (point (env c.mem x) 0 1 2 3) ((n + 1) • Aa) := by
    rw [mc, pb, pa, h.a, succ_nsmul]
    have : point (env a.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
      simp only [point, ha 0 (Or.inl (by decide)), ha 1 (Or.inl (by decide)), ha 2 (Or.inl (by decide)),
        ha 3 (Or.inl (by decide))]
    rw [this]
    exact pointAdd_rep h.value hA
  obtain tpb : ∀ o, o + 128 ≤ 8192 → 1024 ≤ o → tablePoint b.mem x o = tablePoint s.mem x o := fun o h1 h2 =>
    table_point_of_words fun k hk => wd_frame1s hc kab.frame (by decide) (by omega_arith) (Or.inr (by omega_arith))
  refine ⟨by omega_arith, by omega_arith, ?_, te, ?_, ?_, fun j hj => ?_, ?_, ?_, h.frame.trans fall⟩
  · exact hc.keep (by rw [tedi, kd.gpr _ (by decide), kc.edi, kb.keep.edi, ka.edi])
      (by rw [twr, kd.wr, kc.wr, kb.keep.wr, ka.wr]) (by rw [tesp, kd.gpr _ (by decide), kc.esp, kb.keep.esp, ka.esp])
  · rw [tm, table_env hfit kd.frame (by omega_arith) (by omega_arith), mc, hb 16 (by decide),
      ha 16 (Or.inr (by decide))]
    exact h.d
  · rw [tm, table_env hfit kd.frame (by omega_arith) (by omega_arith)]; exact crep
  · rw [tm]
    by_cases hjn : j < n
    · rw [tablePoint_frame hfit kd.frame (by omega_arith) (by omega_arith) (Or.inl (by omega_arith)), mc,
        tpb _ (by omega_arith) (by omega_arith)]
      exact h.table j hjn
    · obtain rfl : j = n := by omega_arith
      rw [pd]; exact crep
  · rw [tm, tablePoint_frame hfit kd.frame (by omega_arith) (by omega_arith) (Or.inr (by omega_arith)), mc,
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
  refine WP.mono (aTableBody_ok (n := 15 - m) (by omega_arith) hA hu) fun v ⟨zv, hv⟩ => ?_
  by_cases h1 : m = 1
  · subst m
    exact .inl ⟨by show v.zf.map (!·) = _; rw [zv]; rfl, hv⟩
  · refine .inr ⟨by show v.zf.map (!·) = _; rw [zv, decide_eq_false (by omega_arith)]; rfl, m - 1, by omega_arith,
      ?_, by omega_arith, by omega_arith⟩
    rw [show 15 - (m - 1) = 15 - m + 1 by omega_arith]; exact hv

/-! ## `-[i]B` -/

theorem negBase_rep (i : Nat) (hi : i < 15) : Rep (negBase i) ((i + 1) • (-baseAff)) := by
  rw [smul_neg]; exact (baseMultiple_rep i hi).neg

/-- A table entry whose dwords are the static's: `-[i + 1]B`. -/
theorem tablePoint_of_dwords {m : Mem} {x : BitVec 32} {i : Nat}
    (h : ∀ k < 32, wd m x (3072 + 4 * (32 * i + k)) = bDword (32 * i + k)) :
    tablePoint m x (3072 + 128 * i) = negBase i := by
  obtain hc : ∀ c < 4, F m x (3072 + 128 * i + 32 * c) = pointCoord (negBase i) c := fun c hc => by
    obtain he : fe m x (3072 + 128 * i + 32 * c) = (pointCoord (negBase i) c).val := by
      unfold fe
      rw [num_congr (g := fun k => (pointCoord (negBase i) c).val / (2 ^ 32) ^ k % 2 ^ 32) (fun k hk => by
        rw [wv, show 3072 + 128 * i + 32 * c + 4 * k = 3072 + 4 * (32 * i + (8 * c + k)) by omega_arith,
          h _ (by omega_arith), bDword, BitVec.toNat_ofNat, show (32 * i + (8 * c + k)) / 32 = i by omega_arith,
          show (32 * i + (8 * c + k)) / 8 % 4 = c by omega_arith, show (32 * i + (8 * c + k)) % 8 = k by omega_arith]),
        num_digits]
      exact Nat.mod_eq_of_lt (by have h := (pointCoord (negBase i) c).isLt; simp only [Spec.X25519.P] at h; omega_arith)
    rw [F, he, VG.Proof.X25519.toFe_self]
  obtain h0 := hc 0 (by decide)
  obtain h1 := hc 1 (by decide)
  obtain h2 := hc 2 (by decide)
  obtain h3 := hc 3 (by decide)
  rw [show 3072 + 128 * i + 32 * 0 = 3072 + 128 * i by omega_arith] at h0
  rw [show 3072 + 128 * i + 32 * 1 = 3072 + 128 * i + 32 by omega_arith] at h1
  rw [show 3072 + 128 * i + 32 * 2 = 3072 + 128 * i + 64 by omega_arith] at h2
  rw [show 3072 + 128 * i + 32 * 3 = 3072 + 128 * i + 96 by omega_arith] at h3
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
  · exact sub_disj (by omega_arith) (by omega_arith) (Or.inl hd)
  · exact (hc.stk rfl (by decide)).2.sub_left (by rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_arith) (by omega_arith))

theorem bTable_ok {x T : BitVec 32} {s : State} (hc : Ctx x s) (hT : BTblAt s x T) (hsym : s.syms bSym = T)
    (hstk : (⟨T.setWidth 64, 1920⟩ : Region).Disjoint (callStk s)) :
    WP isa bTable s fun t => ScalarKeep s t ∧ Frame [sub x 3072 1920, callStk s] s.mem t.mem ∧
      (∀ i < 15, Rep (tablePoint t.mem x (3072 + 128 * i)) ((i + 1) • (-baseAff))) ∧
      env t.mem x 16 = env s.mem x 16 ∧ t.syms = s.syms := by
  have hfit := hc.fit
  obtain hsp := (hc.stk rfl (by decide)).1
  have hTf := hT.fit
  -- The static, apart from what the copy writes.
  obtain hTd : ∀ r ∈ [sub x 3072 1920, callStk s], (⟨T.setWidth 64, 1920⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hT.sc.sub_right (by rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_arith) (by omega_arith))
    · exact hstk
  -- After `n` dwords.
  let LI : Nat → State → Prop := fun n t => ScalarKeep s t ∧ t.syms = s.syms ∧
    t.gpr .esi = T + BitVec.ofNat 32 (4 * n) ∧ t.gpr .edx = x + BitVec.ofNat 32 (3072 + 4 * n) ∧
    t.gpr .ecx = BitVec.ofNat 32 (480 - n) ∧ Frame [sub x 3072 1920, callStk s] s.mem t.mem ∧
    ∀ k < n, wd t.mem x (3072 + 4 * k) = bDword k
  unfold bTable
  refine WP.seq (WP.mono (symFrame_ok bSym s (by omega_arith)) fun s₁ h₁ => ?_)
  refine WP.seq (Wp.wp_mov fun u₁ v₁ => Wp.wp_mov fun u₂ v₂ => Wp.wp_addi fun u₃ v₃ =>
    Wp.wp_movi fun u₄ v₄ => WP.block_nil ?_)
  obtain k₄ : ScalarKeep s u₄ :=
    ⟨by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
        h₁.gpr _ (by decide)],
      by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
        h₁.gpr _ (by decide)],
      by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, h₁.rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, h₁.wr]⟩
  obtain i₀ : LI 0 u₄ := by
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
    obtain ct : Ctx x t := hc.keep kt.edi kt.wr kt.esp
    obtain Tt : BTblAt t x T := hT.of_frame ft hTd (by rw [kt.rd, kt.wr])
    refine Wp.wp_ldm (B := T + BitVec.ofNat 32 (4 * n)) (o := 0) si
      (by rw [show addr (T + BitVec.ofNat 32 (4 * n)) 0 = addr T (4 * n) by
            rw [addr_zero]; rfl]
          exact Tt.inR hn) fun u₁ w₁ => ?_
    refine Wp.wp_stm (B := x + BitVec.ofNat 32 (3072 + 4 * n)) (o := 0) (by rw [w₁.other _ (by decide), di])
      (by rw [show addr (x + BitVec.ofNat 32 (3072 + 4 * n)) 0 = addr x (3072 + 4 * n) by
            rw [addr_zero]; rfl]
          rw [w₁.wr]; exact ct.inW (by omega_arith) (by decide)) fun u₂ w₂ => ?_
    refine Wp.wp_addi fun u₃ w₃ => Wp.wp_addi fun u₄ w₄ => Wp.wp_subi fun u₅ w₅ _ z₅ => WP.block_nil ?_
    obtain ea : addr (x + BitVec.ofNat 32 (3072 + 4 * n)) 0 = addr x (3072 + 4 * n) := by
      rw [addr_zero]; rfl
    obtain ev : u₁.gpr .eax = bDword n := by
      rw [w₁.gpr, show addr (T + BitVec.ofNat 32 (4 * n)) 0 = addr T (4 * n) by
        rw [addr_zero]; rfl]
      exact Tt.val n hn
    obtain m₅ : u₅.mem = t.mem.writeW (addr x (3072 + 4 * n)) (bDword n) := by
      rw [w₅.mem, w₄.mem, w₃.mem, w₂.mem, ea, ev, w₁.mem]
    obtain next : LI (n + 1) u₅ := by
      refine ⟨kt.trans ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
      · rw [w₅.other _ (by decide), w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide)]
      · rw [w₅.other _ (by decide), w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide)]
      · rw [w₅.rd, w₄.rd, w₃.rd, w₂.rd, w₁.rd]
      · rw [w₅.wr, w₄.wr, w₃.wr, w₂.wr, w₁.wr]
      · rw [w₅.syms, w₄.syms, w₃.syms, w₂.syms, w₁.syms, st]
      · rw [w₅.other _ (by decide), w₄.other _ (by decide), w₃.gpr, w₂.gpr, w₁.other _ (by decide), si,
          show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 4 * n + 4 = 4 * (n + 1) by omega_arith]
      · rw [w₅.other _ (by decide), w₄.gpr, w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide), di,
          show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 3072 + 4 * n + 4 = 3072 + 4 * (n + 1) by omega_arith]
      · rw [w₅.gpr, w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide), ci,
          Wp.ofNat_pred (by omega_arith)]
        congr 1
      · rw [m₅]
        exact ft.writeW (List.mem_cons_self) _ (sub_contains (by omega_arith) (by omega_arith) (by omega_arith) (by decide))
      · rw [m₅]
        by_cases e : k = n
        · subst e; exact wd_write_self _ _ _ _
        · rw [wd_write_ne _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
          exact bt k (by omega_arith)
    obtain z : u₅.zf = some (decide (480 - (n + 1) = 0)) := by
      rw [z₅, w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide), ci,
        Wp.ofNat_pred (by omega_arith), Wp.ofNat_beq_zero (by omega_arith)]
      rfl
    by_cases done : n + 1 = 480
    · refine .inl ⟨?_, done ▸ next⟩
      simp only [eval, z, show 480 - (n + 1) = 0 by omega_arith, decide_true, Option.map_some, Bool.not_true]
    · refine .inr ⟨?_, 480 - (n + 1), by omega_arith, n + 1, rfl, by omega_arith, next⟩
      simp only [eval, z, show 480 - (n + 1) ≠ 0 by omega_arith, decide_false, Option.map_some, Bool.not_false]
  · rw [tablePoint_of_dwords fun k hk => bt _ (by omega_arith)]
    exact negBase_rep i hi
  · show F t.mem x (offset 16) = F s.mem x (offset 16)
    refine congrArg VG.Proof.X25519.toFe (num_congr fun k hk => ?_)
    show (wd t.mem x (offset 16 + 4 * k)).toNat = (wd s.mem x (offset 16 + 4 * k)).toNat
    rw [wd_frameT hc ft (by simp only [offset]; omega_arith)]

end VG.Proof.Ed25519.X86

end

end

/-! ### `Ed25519.X86.WindowStep`, which only this module used -/

section

/-!
# Verification's windows

A window doubles the sum four times (`dbl-2008-hwcd`, `dblPoint_rep`), reads a
digit of a scalar from the inputs (its nibble `esi`), and adds the digit's
entry of a table, unless the digit is zero. The sum represents a
multiple of `A` plus a multiple of `-B` throughout (`Rep`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86 (sc at_)

/-! ## Doublings -/

theorem dblOps_eval (e : Env) : point (evalOps dblOps e) 0 1 2 3 = dblPoint (point e 0 1 2 3) := rfl

theorem dbl_ok {s : State} {x : BitVec 32} (hc : Ctx x s) {a : EPoint dZ}
    (h : Rep (point (env s.mem x) 0 1 2 3) a) :
    WP isa dbl s fun t => FieldKeep x s t ∧ Rep (point (env t.mem x) 0 1 2 3) (a + a) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.mono (fieldCode_ok dblOps hc) fun t ⟨kt, vt⟩ => ⟨kt, ?_, fun i hi => ?_⟩
  · rw [vt, dblOps_eval]; exact dblPoint_rep h.proj
  · rw [vt]; exact point_ops_high _ (by decide) _ i hi

/-- `add d, v`, and the carry. -/
theorem wp_addiC {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _) rfl)

/-- The doubling loop's counter: `esi` after `4 - n` of its four iterations, `n` left, and
`2³⁰` added: the next count, carrying out exactly on the last. -/
theorem dblCount_step {e u : BitVec 32} {n : Nat} (he : e.toNat < 2 ^ 30) (h1 : 1 ≤ n) (h4 : n ≤ 4)
    (hu : u.toNat = e.toNat + (4 - n) * 2 ^ 30) :
    (u + 0x40000000).toNat = (e.toNat + (4 - (n - 1)) * 2 ^ 30) % 2 ^ 32 ∧
      (decide (2 ^ 32 ≤ u.toNat + (0x40000000 : BitVec 32).toNat) = decide (n = 1)) := by
  have h30 : (0x40000000 : BitVec 32).toNat = 2 ^ 30 := rfl
  rw [BitVec.toNat_add, hu, h30]
  constructor
  · congr 1; omega_arith
  · simp only [decide_eq_decide]; omega_arith

theorem doubleWindow_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (hesi : (s.gpr .esi).toNat < 2 ^ 30)
    {a : EPoint dZ} (h : Rep (point (env s.mem x) 0 1 2 3) a) :
    WP isa doubleWindow s fun t => IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem x) 0 1 2 3) ((16 : Nat) • a) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.loop (M := isa) (Inv := fun n (t : State) => 1 ≤ n ∧ n ≤ 4 ∧
    (t.gpr .esi).toNat = (s.gpr .esi).toNat + (4 - n) * 2 ^ 30 ∧ IKeep x s t ∧
    Rep (point (env t.mem x) 0 1 2 3) ((2 ^ (4 - n) : Nat) • a) ∧
    ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i) ?_ 4 s
    ⟨by decide, by decide, by simp, IKeep.refl _ _, by simpa using h, fun _ _ => rfl⟩
  intro n t ⟨h1, h4, he, kt, rt, ht⟩
  rw [dblStep, WP.block_append_iff]
  refine WP.mono (dbl_ok (kt.ctx hc) rt) fun u ⟨ku, ru, hu⟩ => ?_
  refine wp_addiC fun v hv cv => WP.block_nil ?_
  obtain eu : (u.gpr .esi).toNat = (s.gpr .esi).toNat + (4 - n) * 2 ^ 30 := by rw [ku.keep.esi]; exact he
  obtain ⟨ev, cv'⟩ := dblCount_step hesi h1 h4 eu
  rw [cv'] at cv
  obtain kv : IKeep x s v := kt.trans ((IKeep.of_field ku).trans (IKeep.of_counter hv))
  obtain rv : Rep (point (env v.mem x) 0 1 2 3) ((2 ^ (4 - (n - 1)) : Nat) • a) := by
    rw [hv.mem, show 4 - (n - 1) = (4 - n) + 1 by omega_arith, pow_succ, mul_comm, ← smul_smul, two_nsmul]
    exact ru
  obtain hv16 : ∀ i : Slot, 16 ≤ i.val → env v.mem x i = env s.mem x i :=
    fun i hi => by rw [hv.mem, hu i hi, ht i hi]
  rw [← hv.gpr] at ev
  by_cases hn : n = 1
  · subst hn
    refine .inl ⟨by simp only [eval, cv]; rfl, kv, ?_, by simpa using rv, hv16⟩
    apply BitVec.eq_of_toNat_eq
    rw [ev]; omega_arith
  · refine .inr ⟨by simp only [eval, cv, hn]; rfl, n - 1, by omega_arith, by omega_arith, by omega_arith,
      by rw [ev, Nat.mod_eq_of_lt (by omega_arith)], kv, rv, hv16⟩

/-! ## Digits -/

/-- What reading a digit leaves: everything but `eax` and the flags. -/
structure EaxKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .eax → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem EaxKeep.trans {s t u : State} (h : EaxKeep s t) (k : EaxKeep t u) : EaxKeep s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.mem.trans h.mem, k.rd.trans h.rd, k.wr.trans h.wr⟩

theorem EaxKeep.of_upd {s t : State} {v : BitVec 32} (h : Wp.Upd s t .eax v) : EaxKeep s t :=
  ⟨h.other, h.mem, h.rd, h.wr⟩

theorem EaxKeep.ikeep {x : BitVec 32} {s t : State} (h : EaxKeep s t) : IKeep x s t :=
  ⟨h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩

theorem bytesAt_getD (m : Mem) (p : Addr) (n i : Nat) (hi : i < n) :
    (Spec.Ed25519.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, hi]

/-- `test d, v`. -/
theorem wp_testi {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Fupd s s' → s'.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

theorem EaxKeep.of_fupd {s t : State} (h : Wp.Fupd s t) : EaxKeep s t :=
  ⟨fun _ _ => by rw [h.gpr], h.mem, h.rd, h.wr⟩

theorem shr1_ofNat {i : Nat} (hi : i < 2 ^ 32) : BitVec.ofNat 32 i >>> 1 = BitVec.ofNat 32 (i / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

theorem and1_beq {i : Nat} (hi : i < 2 ^ 32) :
    (BitVec.ofNat 32 i &&& 1 == 0) = decide (i % 2 = 0) := by
  have : BitVec.ofNat 32 i &&& 1 = BitVec.ofNat 32 (i % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    simp only [BitVec.toNat_ofNat]
    omega_arith
  rw [this, Wp.ofNat_beq_zero (by omega_arith)]

private theorem nibble_fact : ∀ b : BitVec 8,
    b.setWidth 32 >>> 4 = BitVec.ofNat 32 (b.toNat / 16) ∧
    b.setWidth 32 &&& 15 = BitVec.ofNat 32 (b.toNat % 16) := by decide

/-- The address of a nibble's byte: the input's pointer plus half the nibble's index. -/
theorem nibbleAddr_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : Saved s₀ (arg s₀ 3) s)
    {a i : Nat} (ha : a < 4) (hi : i < 2 ^ 32) (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block [.mov .eax (.reg .esi), .shift .shr .eax 1, .alu .add .eax (.mem (at_ .esp (4 + 4 * a)))])
      s fun t => EaxKeep s t ∧ t.gpr .eax = arg s₀ a + BitVec.ofNat 32 (i / 2) := by
  refine Wp.wp_mov fun u₁ h₁ => Wp.wp_shr (by decide) fun u₂ h₂ _ => ?_
  obtain e₂ : u₂.gpr .eax = BitVec.ofNat 32 (i / 2) := by rw [h₂.gpr, h₁.gpr, hesi, shr1_ofNat hi]
  obtain hr₂ : u₂.rd ++ u₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hs.rd, hs.wr]
  refine Wp.wp_addm (B := s₀.gpr .esp) (by rw [h₂.other _ (by decide), h₁.other _ (by decide)]; exact hs.esp)
    (by rw [hr₂]; exact hp.argIn ha) fun t ht => WP.block_nil
      ⟨(EaxKeep.of_upd h₁).trans ((EaxKeep.of_upd h₂).trans (EaxKeep.of_upd ht)), ?_⟩
  rw [ht.gpr, e₂, h₂.mem, h₁.mem, hp.arg_same hs.frame ha, BitVec.add_comm]

/-- The byte of a nibble, and the nibble's parity in ZF. -/
theorem nibbleByte_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : Saved s₀ (arg s₀ 3) s)
    {a add n i : Nat} (ha : a < 4) (hsl : SlicePre s₀ 3 (arg s₀ a + BitVec.ofNat 32 add) n)
    (hi : i < 2 * n) (hn : n ≤ 64) (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block [.mov .eax (.reg .esi), .shift .shr .eax 1, .alu .add .eax (.mem (at_ .esp (4 + 4 * a))),
      .movzx8 .eax (at_ .eax add), .alu .test .esi (.imm 1)]) s fun t => EaxKeep s t ∧
      t.gpr .eax = ((Spec.Ed25519.bytesAt s₀.mem ((arg s₀ a + BitVec.ofNat 32 add).setWidth 64) n).getD
        (i / 2) 0).setWidth 32 ∧ t.zf = some (decide (i % 2 = 0)) := by
  obtain hn : i < 2 ^ 32 := by omega_arith
  show WP isa (.block (([.mov .eax (.reg .esi), .shift .shr .eax 1,
    .alu .add .eax (.mem (at_ .esp (4 + 4 * a)))] : List Instr) ++
    [.movzx8 .eax (at_ .eax add), .alu .test .esi (.imm 1)])) s _
  refine WP.block_append (WP.mono (nibbleAddr_ok hp hs ha hn hesi) fun u₃ ⟨k₃, e₃⟩ => ?_)
  obtain hA : addr (u₃.gpr .eax) add = addr (arg s₀ a + BitVec.ofNat 32 add) (i / 2) := by
    rw [e₃]; simp only [addr]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 (i / 2))]
  obtain hr₃ : u₃.rd ++ u₃.wr = s₀.rd ++ s₀.wr := by rw [k₃.rd, k₃.wr, hs.rd, hs.wr]
  refine scalar_ld8 hA (by rw [hr₃]; exact slice_read hsl (by omega_arith) (by decide)) fun u₄ h₄ =>
    wp_testi fun t ht zt => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact k₃.trans ((EaxKeep.of_upd h₄).trans (EaxKeep.of_fupd ht))
  · rw [ht.gpr, h₄.gpr, k₃.mem, bytesAt_getD _ _ _ _ (by omega_arith), ← addr_eq (by have := hsl.fit; omega_arith)]
    congr 1
    apply hs.frame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hsl.sep _ (slice_contains hsl (by omega_arith) (by decide))
    · exact hsl.stk _ (slice_contains hsl (by omega_arith) (by decide))
  · rw [zt, h₄.other _ (by decide), k₃.gpr _ (by decide), hesi, and1_beq hn]

theorem digitNibble_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : Saved s₀ (arg s₀ 3) s)
    {a add n i : Nat} (ha : a < 4) (hsl : SlicePre s₀ 3 (arg s₀ a + BitVec.ofNat 32 add) n)
    (hi : i < 2 * n) (hn : n ≤ 64) (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (digitNibble (4 + 4 * a) add) s fun t => EaxKeep s t ∧
      t.gpr .eax = BitVec.ofNat 32 (nibbleOf (Spec.Ed25519.bytesAt s₀.mem
        ((arg s₀ a + BitVec.ofNat 32 add).setWidth 64) n) i) := by
  refine WP.seq (WP.mono (nibbleByte_ok hp hs ha hsl hi hn hesi) fun u ⟨ku, eu, zu⟩ => ?_)
  refine WP.ite (!decide (i % 2 = 0)) (by show u.zf.map (!·) = _; rw [zu]; rfl) (fun h => ?_) (fun h => ?_)
  · have h1 : i % 2 = 1 := by simp at h; omega_arith
    refine Wp.wp_shr (by decide) fun t ht _ => WP.block_nil ⟨ku.trans (EaxKeep.of_upd ht), ?_⟩
    rw [ht.gpr, eu, (nibble_fact _).1, nibbleOf, ite_eq_left h1]
  · have h0 : ¬ i % 2 = 1 := by simp at h; omega_arith
    refine Wp.wp_andi fun t ht => WP.block_nil ⟨ku.trans (EaxKeep.of_upd ht), ?_⟩
    rw [ht.gpr, eu, (nibble_fact _).2, nibbleOf, ite_eq_right h0]

/-! ## Adding a digit's entry -/

theorem entryAddr_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o : Nat) {v : Nat} (hv : 1 ≤ v)
    (hv' : v < 16) (he : s.gpr .eax = BitVec.ofNat 32 v) :
    WP isa (.block (entryAddr o)) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 (o + 128 * (v - 1)) := by
  refine Wp.wp_subi fun s₁ h₁ _ _ => Wp.wp_movi fun s₂ h₂ => wp_mul fun s₃ h₃ => ?_
  refine Wp.wp_add fun s₄ h₄ _ => Wp.wp_addi fun s₅ h₅ => Wp.wp_mov fun s₆ h₆ => WP.block_nil ?_
  obtain hk : Keep s s₆ := (updKeep h₁).trans ((updKeep h₂).trans (h₃.keep.trans
    ((updKeep h₄).trans ((updKeep h₅).trans (updKeep h₆)))))
  obtain e₁ : s₁.gpr .eax = BitVec.ofNat 32 (v - 1) := by rw [h₁.gpr, he]; exact Wp.ofNat_pred hv
  obtain hvv : s₃.gpr .eax = BitVec.ofNat 32 (128 * (v - 1)) := by
    apply BitVec.eq_of_toNat_eq
    change VG.Proof.X25519.X86.v s₃ .eax = _
    rw [h₃.eax]
    simp only [VG.Proof.X25519.X86.v, h₂.other .eax (by decide), e₁, h₂.gpr, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show v - 1 < 2 ^ 32 by omega_arith)]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm (v - 1) 128)
  refine ⟨hk, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  rw [h₆.gpr, h₅.gpr, h₄.gpr, hvv, h₃.other .edi (by decide) (by decide),
    h₂.other .edi (by decide), h₁.other .edi (by decide), hc.edi]
  rw [BitVec.add_comm (BitVec.ofNat 32 (128 * (v - 1))) x, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.add_comm (128 * (v - 1)) o]

theorem digit_test_fact : ∀ v < 16, (BitVec.ofNat 32 v &&& BitVec.ofNat 32 v == 0) = decide (v = 0) := by
  decide

theorem addDigit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat} (ho : 1024 ≤ o)
    (hn : o + 1920 ≤ 8192) {v : Nat} (hv : v < 16) (he : s.gpr .eax = BitVec.ofNat 32 v)
    {X a : EPoint dZ} (htab : ∀ j < 15, Rep (tablePoint s.mem x (o + 128 * j)) ((j + 1) • X))
    (hacc : Rep (point (env s.mem x) 0 1 2 3) a) (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (addDigit o) s fun t => IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem x) 0 1 2 3) (a + v • X) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  obtain htest : WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t =>
      IKeep x s t ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.zf = some (decide (v = 0)) :=
    Wp.wp_test fun t ht zt => WP.block_nil ⟨⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
      by rw [ht.mem]; exact Frame.refl _ _⟩, ht.mem, ht.gpr, by rw [zt, he, digit_test_fact v hv]⟩
  refine WP.seq (WP.mono htest fun u ⟨ku, mu, gu, zu⟩ => ?_)
  obtain cu := ku.ctx hc
  refine WP.ite (!decide (v = 0)) (by show u.zf.map (!·) = _; rw [zu]; rfl) (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := by simpa using h
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (entryAddr_ok cu o (by omega_arith) hv (by rw [gu]; exact he)) fun b ⟨kb, mb, pb⟩ => ?_
    obtain cb := kb.ctx cu
    refine WP.mono (pointFromTableQ_ok cb pb (by omega_arith) (by omega_arith)) fun c ⟨kc, ec, pc, hc'⟩ => ?_
    obtain cc := kc.ctx cb
    refine WP.mono (pointAddCall_ok cc (by rw [hc' 16 (Or.inr (by decide)), mb, mu]; exact hd))
      fun t ⟨kt, pt, ht⟩ => ⟨((ku.trans (IKeep.of_mem kb mb)).trans kc).trans (IKeep.of_call kt), ?_, ?_,
        fun i hi => ?_⟩
    · rw [kt.keep.esi, ec, kb.esi, gu]
    · have p0 : point (env c.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
        simp only [point, hc' 0 (Or.inl (by decide)), hc' 1 (Or.inl (by decide)),
          hc' 2 (Or.inl (by decide)), hc' 3 (Or.inl (by decide)), mb, mu]
      rw [pt, p0, pc, mb, mu]
      have := htab (v - 1) (by omega_arith)
      rw [show v - 1 + 1 = v by omega_arith] at this
      exact pointAdd_rep hacc this
    · rw [ht i hi, hc' i (Or.inr (by omega_arith)), mb, mu]
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    refine WP.block_nil ⟨ku, by rw [gu], ?_, fun i _ => by rw [mu]⟩
    rw [mu, zero_smul, add_zero]; exact hacc

/-! ## Windows -/

/-- What the windows keep: the saved state, `d`, both tables and `R`. -/
structure WinCtx (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (s : State) : Prop where
  pre : VerifyPre s₀
  saved : Saved s₀ (arg s₀ 3) s
  d : env s.mem (arg s₀ 3) 16 = Spec.Ed25519.d
  ta : ∀ j < 15, Rep (tablePoint s.mem (arg s₀ 3) (1024 + 128 * j)) ((j + 1) • Aa)
  tb : ∀ j < 15, Rep (tablePoint s.mem (arg s₀ 3) (3072 + 128 * j)) ((j + 1) • (-baseAff))
  r : tablePoint s.mem (arg s₀ 3) 7808 = R

theorem WinCtx.ctx {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) : Ctx (arg s₀ 3) s :=
  h.saved.ctx h.pre.scratch.fit h.pre.scratch.wr h.pre.scratch.stk

theorem WinCtx.of_ikeep {s₀ s t : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) (k : IKeep (arg s₀ 3) s t)
    (hd : env t.mem (arg s₀ 3) 16 = env s.mem (arg s₀ 3) 16) : WinCtx s₀ Aa R t := by
  have hfit := h.pre.scratch.fit
  refine ⟨h.pre, h.saved.ikeep hfit k, hd.trans h.d, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rw [workspace_table k h.ctx _ (by omega_arith) (by omega_arith)]; exact h.ta j hj
  · rw [workspace_table k h.ctx _ (by omega_arith) (by omega_arith)]; exact h.tb j hj
  · rw [workspace_table k h.ctx _ (by decide) (by decide)]; exact h.r

end VG.Proof.Ed25519.X86

end

end


/-!
# Verification's windows: the nibbles and the loops

After the bytes of the scalars from `i` up, the sum represents
`[k / 256^i]A + [S / 256^i](-B)` (`wsum`), and after their nibbles from `n`
up, `[k / 16^n]A + [S / 16^n](-B)` (`nsum`). The leading zero bytes of `k`
above its low 32 are skipped, where the sum is zero; then each window takes
one nibble of both scalars, `S` having none from 64 up (`S < 256^32`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

abbrev verificationScalar (s : State) : Nat := Spec.Ed25519.decodeLE
  (Spec.Ed25519.bytesAt s.mem ((arg s 1 + BitVec.ofNat 32 32).setWidth 64) 32)
abbrev verificationChallenge (s : State) : Nat := Spec.Ed25519.decodeLE
  (Spec.Ed25519.bytesAt s.mem ((arg s 2 + BitVec.ofNat 32 0).setWidth 64) 64)

/-- Byte `i` of `k`. -/
abbrev kByte (s₀ : State) (i : Nat) : Byte :=
  (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 2 + BitVec.ofNat 32 0).setWidth 64) 64).getD i 0

/-- The sum after the bytes from `i` up. -/
def wsum (s₀ : State) (Aa : EPoint dZ) (i : Nat) : EPoint dZ :=
  (verificationChallenge s₀ / 256 ^ i) • Aa + (verificationScalar s₀ / 256 ^ i) • (-baseAff)

theorem kByte_val (s₀ : State) (i : Nat) :
    (kByte s₀ i).toNat = verificationChallenge s₀ / 256 ^ i % 256 := (decodeLE_byte _ i).symm

/-- The sum after the nibbles from `n` up. -/
def nsum (s₀ : State) (Aa : EPoint dZ) (n : Nat) : EPoint dZ :=
  (verificationChallenge s₀ / 16 ^ n) • Aa + (verificationScalar s₀ / 16 ^ n) • (-baseAff)

theorem nsum_two_mul (s₀ : State) (Aa : EPoint dZ) (c : Nat) : nsum s₀ Aa (2 * c) = wsum s₀ Aa c := by
  simp only [nsum, wsum, div_pow16_two_mul]

/-- Nibble `n` of `k`. -/
def kNib (s₀ : State) (n : Nat) : Nat :=
  nibbleOf (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 2 + BitVec.ofNat 32 0).setWidth 64) 64) n

/-- Nibble `n` of `S`. -/
def sNib (s₀ : State) (n : Nat) : Nat :=
  nibbleOf (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1 + BitVec.ofNat 32 32).setWidth 64) 32) n

theorem kNib_lt (s₀ : State) (n : Nat) : kNib s₀ n < 16 := nibbleOf_lt _ _

theorem sNib_lt (s₀ : State) (n : Nat) : sNib s₀ n < 16 := nibbleOf_lt _ _

theorem kNib_val (s₀ : State) (n : Nat) : kNib s₀ n = verificationChallenge s₀ / 16 ^ n % 16 :=
  (decodeLE_nibble _ n).symm

theorem sNib_val (s₀ : State) (n : Nat) : sNib s₀ n = verificationScalar s₀ / 16 ^ n % 16 :=
  (decodeLE_nibble _ n).symm

/-- `S` has no nibble from 64 up. -/
theorem sNib_high (s₀ : State) {n : Nat} (hn : 64 ≤ n) : sNib s₀ n = 0 := by
  rw [sNib_val, nibble_high_zero (decodeLE_lt32 _ _) hn]

/-- `k`'s nibble `n`. -/
theorem digitK_ok {s₀ : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 128)
    (t : State) (ht : WinCtx s₀ Aa R t) (et : t.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (digitNibble 12 0) t fun u => EaxKeep t u ∧ u.gpr .eax = BitVec.ofNat 32 (kNib s₀ n) :=
  digitNibble_ok (a := 2) ht.pre.scratch ht.saved (by decide) ht.pre.challenge (by omega_arith) (by decide) et

/-- `S`'s nibble `n`. -/
theorem digitS_ok {s₀ : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 64)
    (t : State) (ht : WinCtx s₀ Aa R t) (et : t.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (digitNibble 8 32) t fun u => EaxKeep t u ∧ u.gpr .eax = BitVec.ofNat 32 (sNib s₀ n) :=
  digitNibble_ok (a := 1) ht.pre.scratch ht.saved (by decide) ht.pre.scalar (by omega_arith) (by decide) et

/-- The nibble counter leaves the top two bits of `esi` to the doublings' loop. -/
theorem esi_lt {s : State} {i : Nat} (hi : i < 2 ^ 30) (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    (s.gpr .esi).toNat < 2 ^ 30 := by
  rw [hesi, BitVec.toNat_ofNat]; omega_arith

/-- `cmp esi, 64`: CF is set exactly below `S`'s 64 nibbles. -/
theorem cmp64_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} (h : WinCtx s₀ Aa R s)
    {n : Nat} (hn : n < 128) (hesi : s.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (.block [.alu .cmp .esi (.imm 64)]) s fun t => WinCtx s₀ Aa R t ∧
      t.gpr .esi = s.gpr .esi ∧ t.mem = s.mem ∧ t.cf = some (decide (n < 64)) :=
  Wp.wp_cmpi fun t ht ct _ => WP.block_nil ⟨h.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr], ht.mem,
    by rw [ct, hesi, Wp.toNat_ofNat_lt (by omega_arith)]; rfl⟩

/-- `S`'s digit added, below its 64 nibbles. -/
theorem addS_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} (h : WinCtx s₀ Aa R s)
    {n : Nat} (hn : n < 128) (hesi : s.gpr .esi = BitVec.ofNat 32 n) {a : EPoint dZ}
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) a) :
    WP isa addS s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (a + sNib s₀ n • (-baseAff)) := by
  refine WP.seq (WP.mono (cmp64_ok h hn hesi) fun u ⟨wu, eu, mu, cu⟩ => ?_)
  obtain ru : Rep (point (env u.mem (arg s₀ 3)) 0 1 2 3) a := by rw [mu]; exact hacc
  refine WP.ite (decide (n < 64)) cu (fun hh => ?_) (fun hh => ?_)
  · have h64 : n < 64 := by simpa using hh
    refine WP.seq (WP.mono (digitS_ok h64 u wu (eu.trans hesi)) fun c ⟨kc, ec⟩ => ?_)
    obtain wc := wu.of_ikeep kc.ikeep (by rw [kc.mem])
    obtain rc : Rep (point (env c.mem (arg s₀ 3)) 0 1 2 3) a := by rw [kc.mem]; exact ru
    refine WP.mono (addDigit_ok wc.ctx (by decide) (by decide) (nibbleOf_lt _ _) ec wc.tb rc wc.d)
      fun t ⟨kt, et, rt, ht⟩ => ⟨wc.of_ikeep kt (ht 16 (by decide)), ?_, rt⟩
    rw [et, kc.gpr _ (by decide)]; exact eu
  · have h64 : 64 ≤ n := by simp at hh; omega_arith
    refine WP.block_nil ⟨wu, eu, ?_⟩
    rw [sNib_high s₀ h64, zero_smul, add_zero]; exact ru

/-- `k`'s digit added. -/
theorem addK_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} (h : WinCtx s₀ Aa R s)
    {n : Nat} (hn : n < 128) (hesi : s.gpr .esi = BitVec.ofNat 32 n) {a : EPoint dZ}
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) a) :
    WP isa addK s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (a + kNib s₀ n • Aa) := by
  refine WP.seq (WP.mono (digitK_ok hn s h hesi) fun c ⟨kc, ec⟩ => ?_)
  obtain wc := h.of_ikeep kc.ikeep (by rw [kc.mem])
  obtain rc : Rep (point (env c.mem (arg s₀ 3)) 0 1 2 3) a := by rw [kc.mem]; exact hacc
  refine WP.mono (addDigit_ok wc.ctx (by decide) (by decide) (nibbleOf_lt _ _) ec wc.ta rc wc.d)
    fun t ⟨kt, et, rt, ht⟩ => ⟨wc.of_ikeep kt (ht 16 (by decide)), ?_, rt⟩
  rw [et, kc.gpr _ (by decide)]

theorem esiDec_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} (h : WinCtx s₀ Aa R s)
    {i : Nat} (hesi : s.gpr .esi = BitVec.ofNat 32 (i + 1)) :
    WP isa (.block [.alu .sub .esi (.imm 1)]) s fun u => WinCtx s₀ Aa R u ∧
      u.gpr .esi = BitVec.ofNat 32 i ∧ u.mem = s.mem :=
  Wp.wp_subi fun u hu _ _ => WP.block_nil ⟨h.of_ikeep (IKeep.of_counter hu) (by rw [hu.mem]),
    by rw [hu.gpr, hesi, Wp.ofNat_pred (by omega_arith), Nat.add_sub_cancel], hu.mem⟩

theorem test_zero (i : Nat) (hi : i < 2 ^ 32) :
    (BitVec.ofNat 32 i &&& BitVec.ofNat 32 i == 0) = decide (i = 0) := by
  rw [BitVec.and_self, Wp.ofNat_beq_zero hi]

/-- A window: the nibble below `n + 1`. -/
theorem nibbleStep_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {n : Nat} (hn : n < 128) (hesi : s.gpr .esi = BitVec.ofNat 32 (n + 1))
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa (n + 1))) :
    WP isa nibbleStep s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      t.zf = some (decide (n = 0)) ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa n) := by
  refine WP.seq (WP.mono (esiDec_ok h hesi) fun u ⟨wu, eu, mu⟩ => ?_)
  obtain ru : Rep (point (env u.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa (n + 1)) := by rw [mu]; exact hacc
  refine WP.seq (WP.mono (doubleWindow_ok wu.ctx (esi_lt (by omega_arith) eu) ru) fun b ⟨kb, eb, rb, hb⟩ => ?_)
  obtain wb := wu.of_ikeep kb (hb 16 (by decide))
  obtain ebs : b.gpr .esi = BitVec.ofNat 32 n := eb.trans eu
  refine WP.seq (WP.mono (addK_ok wb hn ebs rb) fun d ⟨wd, ed, rd⟩ => ?_)
  refine WP.seq (WP.mono (addS_ok wd hn (ed.trans ebs) rd) fun e ⟨we, ee, re⟩ => ?_)
  refine Wp.wp_test fun t ht zt => WP.block_nil ⟨we.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd,
    ht.wr, by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), ?_, ?_, ?_⟩
  · rw [ht.gpr, ee, ed, ebs]
  · rw [zt, ee, ed, ebs, test_zero n (by omega_arith)]
  · rw [ht.mem, nsum, ← nibble_step Aa (-baseAff) (verificationChallenge s₀) (verificationScalar s₀) n,
      ← kNib_val, ← sNib_val]
    exact re

/-! ## The loop -/

theorem loopN_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {c : Nat} (hc0 : 0 < c) (hc : c ≤ 128) (hesi : s.gpr .esi = BitVec.ofNat 32 c)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa c)) :
    WP isa (.loop nibbleStep .ne) s fun t => WinCtx s₀ Aa R t ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa 0) := by
  refine WP.loop (M := isa) (Inv := fun m t => WinCtx s₀ Aa R t ∧ 0 < m ∧ m ≤ 128 ∧
    t.gpr .esi = BitVec.ofNat 32 m ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa m)) ?_ c s
    ⟨h, hc0, hc, hesi, hacc⟩
  intro m u ⟨wu, hm0, hm, eu, ru⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega_arith⟩
  refine WP.mono (nibbleStep_ok wu (by omega_arith) eu ru) fun t ⟨wt, et, zt, rt⟩ => ?_
  by_cases hi : i = 0
  · subst hi
    exact .inl ⟨by show t.zf.map (!·) = _; rw [zt]; rfl, wt, rt⟩
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt, decide_eq_false hi]; rfl, i, by omega_arith,
      wt, by omega_arith, by omega_arith, et, rt⟩

/-- `add esi, esi`: the bytes left to the nibbles left. -/
theorem nibbles_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {c : Nat}
    (h : WinCtx s₀ Aa R s) (hesi : s.gpr .esi = BitVec.ofNat 32 c) :
    WP isa (.block [.alu .add .esi (.reg .esi)]) s fun t => WinCtx s₀ Aa R t ∧
      t.gpr .esi = BitVec.ofNat 32 (2 * c) ∧ t.mem = s.mem :=
  Wp.wp_add fun t ht _ => WP.block_nil ⟨h.of_ikeep (IKeep.of_counter ht) (by rw [ht.mem]),
    by rw [ht.gpr, hesi, ← BitVec.ofNat_add, Nat.two_mul], ht.mem⟩

/-! ## Skipping the leading zero bytes of `k` -/

theorem skipLoad_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {c : Nat} (hc : 1 ≤ c) (hc' : c ≤ 64) (hesi : s.gpr .esi = BitVec.ofNat 32 c) :
    WP isa (.block skipLoad) s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 c ∧
      t.gpr .edx = BitVec.ofNat 32 (c - 1) ∧ t.zf = some (decide ((kByte s₀ (c - 1)).toNat = 0)) ∧
      t.mem = s.mem := by
  have hp := h.pre
  have hs := h.saved
  refine Wp.wp_mov fun u₁ h₁ => Wp.wp_subi fun u₂ h₂ _ _ => ?_
  obtain e₂ : u₂.gpr .edx = BitVec.ofNat 32 (c - 1) := by
    rw [h₂.gpr, h₁.gpr, hesi]; exact Wp.ofNat_pred hc
  obtain hsp : u₂.gpr .esp = s₀.gpr .esp := by
    rw [h₂.other _ (by decide), h₁.other _ (by decide)]; exact hs.esp
  obtain hr₂ : u₂.rd ++ u₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hs.rd, hs.wr]
  refine Wp.wp_ldm hsp (by rw [hr₂]; exact hp.scratch.argIn (i := 2) (by decide)) fun u₃ h₃ => ?_
  obtain m₂ : u₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  obtain e₃ : u₃.gpr .eax = arg s₀ 2 := by
    rw [h₃.gpr, m₂, show (12 : Nat) = 4 + 4 * 2 from rfl]; exact hp.scratch.arg_same hs.frame (by decide)
  refine Wp.wp_add fun u₄ h₄ _ => ?_
  obtain e₄ : u₄.gpr .eax = arg s₀ 2 + BitVec.ofNat 32 (c - 1) := by
    rw [h₄.gpr, e₃, h₃.other .edx (by decide), e₂]
  obtain hA : addr (u₄.gpr .eax) 0 = addr (arg s₀ 2 + BitVec.ofNat 32 0) (c - 1) := by
    rw [e₄]; simp only [addr]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 (c - 1))]
  obtain hr₄ : u₄.rd ++ u₄.wr = s₀.rd ++ s₀.wr := by rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr, hr₂]
  refine scalar_ld8 hA (by rw [hr₄]; exact slice_read hp.challenge (by omega_arith) (by decide))
    fun u₅ h₅ => Wp.wp_test fun t ht zt => WP.block_nil ?_
  have hsl := hp.challenge
  obtain byte : s.mem (addr (arg s₀ 2 + BitVec.ofNat 32 0) (c - 1)) = kByte s₀ (c - 1) := by
    rw [kByte, bytesAt_getD _ _ _ _ (by omega_arith), ← addr_eq (by have := hsl.fit; omega_arith)]
    apply hs.frame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hsl.sep _ (slice_contains hsl (by omega_arith) (by decide))
    · exact hsl.stk _ (slice_contains hsl (by omega_arith) (by decide))
  obtain mt : t.mem = s.mem := by rw [ht.mem, h₅.mem, h₄.mem, h₃.mem, m₂]
  obtain k₅ : IKeep (arg s₀ 3) s t := ⟨by rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide),
      h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)],
    by rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
      h₂.other _ (by decide), h₁.other _ (by decide)],
    by rw [ht.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [ht.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
    by rw [mt]; exact Frame.refl _ _⟩
  refine ⟨h.of_ikeep k₅ (by rw [mt]), ?_, ?_, ?_, mt⟩
  · rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
      h₂.other _ (by decide), h₁.other _ (by decide), hesi]
  · rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), e₂]
  · rw [zt, h₅.gpr, h₄.mem, h₃.mem, m₂, byte, BitVec.and_self]
    generalize kByte s₀ (c - 1) = b
    revert b; decide

/-- With `c` bytes of the scalars left. -/
def LoopAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (c : Nat) (t : State) : Prop :=
  WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 c ∧
    Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa c)

/-- Skipping, with `32 + m` bytes of `k` left, all of them above zero. -/
def SkipAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (m : Nat) (t : State) : Prop :=
  WinCtx s₀ Aa R t ∧ 0 < m ∧ m ≤ 32 ∧ t.gpr .esi = BitVec.ofNat 32 (32 + m) ∧
    verificationChallenge s₀ / 256 ^ (32 + m) = 0 ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0

/-- Whether the skipping goes on below `32 + m` bytes: the byte below is zero, and not the last
of `k` alone. -/
def skipOn (s₀ : State) (m : Nat) : Bool :=
  decide ((kByte s₀ (32 + m - 1)).toNat = 0) && decide (m ≠ 1)

/-- Where the skipping stops, if it does below `32 + m` bytes. -/
def skipEnd (s₀ : State) (m : Nat) : Nat :=
  if (kByte s₀ (32 + m - 1)).toNat = 0 then 32 + m - 1 else 32 + m

theorem wsum_zero {s₀ : State} {Aa : EPoint dZ} {c : Nat} (hc : 32 ≤ c)
    (hk : verificationChallenge s₀ / 256 ^ c = 0) : wsum s₀ Aa c = 0 := by
  rw [wsum, hk, high_zero (decodeLE_lt32 _ _) hc, zero_smul, zero_smul, add_zero]

theorem skipBody_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {m : Nat}
    (h : SkipAt s₀ Aa R m s) :
    WP isa skipBody s fun t => t.zf.map (!·) = some (skipOn s₀ m) ∧
      (skipOn s₀ m = false → 32 ≤ skipEnd s₀ m ∧ skipEnd s₀ m ≤ 64 ∧ LoopAt s₀ Aa R (skipEnd s₀ m) t) ∧
      (skipOn s₀ m = true → SkipAt s₀ Aa R (m - 1) t) := by
  obtain ⟨wu, hm0, hm, eu, ku, ru⟩ := h
  refine WP.seq (WP.mono (skipLoad_ok wu (by omega_arith) (by omega_arith) eu) fun v ⟨wv, ev, dv, zv, mv⟩ => ?_)
  obtain rv : Rep (point (env v.mem (arg s₀ 3)) 0 1 2 3) 0 := by rw [mv]; exact ru
  refine WP.ite (!decide ((kByte s₀ (32 + m - 1)).toNat = 0)) (by show v.zf.map (!·) = _; rw [zv]; rfl)
    (fun hh => ?_) (fun hh => ?_)
  · have hnz : (kByte s₀ (32 + m - 1)).toNat ≠ 0 := by simpa using hh
    obtain son : skipOn s₀ m = false := by simp only [skipOn, decide_eq_false hnz, Bool.false_and]
    obtain sen : skipEnd s₀ m = 32 + m := by simp only [skipEnd, hnz, ↓reduceIte]
    refine Wp.wp_cmp fun t ht _ zt => WP.block_nil ⟨?_, fun _ => ?_, fun h => absurd h (by rw [son]; decide)⟩
    · rw [zt, son]; simp
    · rw [sen]
      refine ⟨by omega_arith, by omega_arith, wv.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
        by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr, ev], ?_⟩
      rw [ht.mem, wsum_zero (by omega_arith) ku]; exact rv
  · have hz : (kByte s₀ (32 + m - 1)).toNat = 0 := by simpa using hh
    obtain k' : verificationChallenge s₀ / 256 ^ (32 + m - 1) = 0 := by
      have := div_split (verificationChallenge s₀) (32 + m - 1)
      rw [show 32 + m - 1 + 1 = 32 + m by omega_arith, ku, ← kByte_val, hz] at this
      exact this
    obtain son : skipOn s₀ m = decide (m ≠ 1) := by
      simp only [skipOn, decide_eq_true hz, Bool.true_and]
    obtain sen : skipEnd s₀ m = 32 + m - 1 := by simp only [skipEnd, hz, ↓reduceIte]
    refine Wp.wp_mov fun w hw => Wp.wp_cmpi fun t ht _ zt => WP.block_nil ?_
    obtain ww : WinCtx s₀ Aa R t := (wv.of_ikeep (IKeep.of_counter hw) (by rw [hw.mem])).of_ikeep
      ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr, by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem])
    obtain et : t.gpr .esi = BitVec.ofNat 32 (32 + m - 1) := by rw [ht.gpr, hw.gpr, dv]
    obtain rt : Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0 := by rw [ht.mem, hw.mem]; exact rv
    obtain zt' : t.zf = some (decide (32 + m - 1 = 32)) := by
      rw [zt, hw.gpr, dv, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
        Wp.sub_beq (by omega_arith) (by omega_arith)]
    refine ⟨?_, fun hf => ?_, fun hn => ?_⟩
    · rw [zt', son]
      by_cases h1 : m = 1
      · subst h1; rfl
      · rw [decide_eq_false (show ¬(32 + m - 1 = 32) by omega_arith), decide_eq_true h1]; rfl
    · have h1 : m = 1 := by
        rw [son] at hf
        by_contra hne
        rw [decide_eq_true hne] at hf
        cases hf
      subst h1
      rw [sen]
      exact ⟨by decide, by decide, ww, et, by rw [wsum_zero (le_refl _) k']; exact rt⟩
    · have h1 : m ≠ 1 := by
        rw [son] at hn
        exact of_decide_eq_true hn
      exact ⟨ww, by omega_arith, by omega_arith, by rw [et]; congr 1; omega_arith,
        by rw [show 32 + (m - 1) = 32 + m - 1 by omega_arith]; exact k', rt⟩

theorem skipZero_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) (hesi : s.gpr .esi = BitVec.ofNat 32 64)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) 0) :
    WP isa skipZero s fun t => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ LoopAt s₀ Aa R c t := by
  obtain high_zero_64 : verificationChallenge s₀ / 256 ^ (32 + 32) = 0 := Nat.div_eq_of_lt (decodeLE_lt64 _ _)
  refine WP.loop (M := isa) (Inv := fun m t => SkipAt s₀ Aa R m t) ?_ 32 s
    ⟨h, by decide, by decide, hesi, high_zero_64, hacc⟩
  intro m u hu
  have hm0 := hu.2.1
  refine WP.mono (skipBody_ok hu) fun t ⟨zt, ft, tt⟩ => ?_
  cases hs : skipOn s₀ m
  · exact .inl ⟨by show t.zf.map (!·) = _; rw [zt, hs], skipEnd s₀ m, ft hs⟩
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt, hs], m - 1, by omega_arith, tt hs⟩

/-! ## The whole multiplication -/

theorem Saved.frame2s {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s) (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (hk : ScalarKeep s t) {o n o' n' : Nat} (hf : Frame [sub x o n, sub x o' n', callStk s] s.mem t.mem)
    (h1 : 16 ≤ o) (h2 : o + n ≤ 8192) (h3 : 16 ≤ o') (h4 : o' + n' ≤ 8192) (h5 : o < 8192)
    (h6 : o' < 8192) : Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (by rw [scR_eq]; exact sub_sub hx (Nat.zero_le _) h2 h5)
    · exact .inl (by rw [scR_eq]; exact sub_sub hx (Nat.zero_le _) h4 h6)
    · exact .inr rfl
  · intro p hp r hr
    have := savedSlots_bound p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))
    · exact sub_disj (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))
    · rw [callStk, h.esp]
      exact h.stk.2.sub_left (by rw [scR_eq]; exact sub_sub hx (Nat.zero_le _) (by omega_arith) (by omega_arith))

theorem windowPrep_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s)
    {A R : Spec.Ed25519.Point} {Aa : EPoint dZ} (hA : Rep A Aa)
    (ha : tablePoint s.mem (arg s₀ 3) 7680 = A) (hr : tablePoint s.mem (arg s₀ 3) 7808 = R)
    (htb : ∀ j < 15, Rep (tablePoint s.mem (arg s₀ 3) (3072 + 128 * j)) ((j + 1) • (-baseAff))) :
    WP isa windowPrep s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 64 ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0 := by
  have hfit := hp.scratch.fit
  obtain hc := hs.ctx hfit hp.scratch.wr hp.scratch.stk
  refine WP.seq (WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] hc) fun a ⟨ka, ea⟩ => ?_)
  obtain sa := hs.ikeep hfit (IKeep.of_field ka)
  obtain ca := ka.ctx hc
  obtain tpa : ∀ o, 928 ≤ o → o + 128 ≤ 8192 → tablePoint a.mem (arg s₀ 3) o = tablePoint s.mem (arg s₀ 3) o :=
    fun o h1 h2 => tablePoint_frame hfit ka.frame (by decide) h2 (Or.inr h1)
  refine WP.seq (WP.mono (aTable_ok ca hA (by rw [tpa 7680 (by decide) (by decide)]; exact ha)
    (by rw [ea]; rfl)) fun b hb => ?_)
  obtain sb := sa.frame2s hfit hb.keep hb.frame (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  obtain cb := sb.ctx hfit hp.scratch.wr hp.scratch.stk
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ cb) fun d ⟨kd, ed⟩ => ?_
  refine Wp.wp_movi fun e he => WP.block_nil ?_
  obtain ke : IKeep (arg s₀ 3) b e := (IKeep.of_field kd).trans (IKeep.of_counter he)
  obtain de : env e.mem (arg s₀ 3) 16 = env b.mem (arg s₀ 3) 16 := by rw [he.mem, ed]; rfl
  refine ⟨⟨hp, sb.ikeep hfit ke, de.trans hb.d, fun j hj => ?_, fun j hj => ?_, ?_⟩, he.gpr, ?_⟩
  · rw [workspace_table ke cb _ (by omega_arith) (by omega_arith)]
    exact hb.table j hj
  · rw [workspace_table ke cb _ (by omega_arith) (by omega_arith),
      tablePoint_frame2s ca hb.frame (by decide) (by decide) (by omega_arith) (Or.inr (by omega_arith)) (Or.inr (by omega_arith)),
      tpa _ (by omega_arith) (by omega_arith)]
    exact htb j hj
  · rw [workspace_table ke cb _ (by decide) (by decide),
      tablePoint_frame2s ca hb.frame (by decide) (by decide) (by decide) (Or.inr (by decide))
        (Or.inr (by decide)), tpa 7808 (by decide) (by decide)]
    exact hr
  · rw [he.mem, ed, constPoint_eval]; exact identity_rep

theorem windowMultiply_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s)
    {A R : Spec.Ed25519.Point} {Aa : EPoint dZ} (hA : Rep A Aa)
    (ha : tablePoint s.mem (arg s₀ 3) 7680 = A) (hr : tablePoint s.mem (arg s₀ 3) 7808 = R)
    (htb : ∀ j < 15, Rep (tablePoint s.mem (arg s₀ 3) (3072 + 128 * j)) ((j + 1) • (-baseAff))) :
    WP isa windowMultiply s fun t => WinCtx s₀ Aa R t ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3)
        (verificationChallenge s₀ • Aa + verificationScalar s₀ • (-baseAff)) := by
  refine WP.seq (WP.mono (windowPrep_ok hp hs hA ha hr htb) fun e ⟨we, ee, re⟩ => ?_)
  refine WP.seq (WP.mono (skipZero_ok we ee re) fun f ⟨c', hc1, hc2, wf, ef, rf⟩ => ?_)
  refine WP.seq (WP.mono (nibbles_ok wf ef) fun g ⟨wg, eg, mg⟩ => ?_)
  refine WP.mono (loopN_ok wg (by omega_arith) (by omega_arith) eg (by rw [mg, nsum_two_mul]; exact rf))
    fun t ⟨wt, rt⟩ => ⟨wt, ?_⟩
  simpa only [nsum, pow_zero, Nat.div_one] using rt

end VG.Proof.Ed25519.X86
