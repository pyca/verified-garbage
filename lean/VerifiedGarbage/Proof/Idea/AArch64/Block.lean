import VerifiedGarbage.Proof.Idea.AArch64.Round

/-!
# IDEA on AArch64: a block

`cryptBlock_run`: `Impl.Idea.AArch64.cryptBlock` replaces the block at `x1`
with `Spec.Idea.cryptBlock` of it under the subkeys at `x0`.
-/

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.Impl.Idea.AArch64

/-! ## Loading -/

/-- The bytes of the block at `a` can be read. -/
def BlockRead (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 i) 1

theorem BlockRead.keep {rs : List Reg} {s s' : State} {a : Addr} (h : BlockRead s a)
    (hk : Keep rs s s') : BlockRead s' a := by
  intro i hi; rw [hk.rd, hk.wr]; exact h i hi

theorem bytes16' (x y : BitVec 8) :
    ((x.setWidth 32).setWidth 64 <<< 8 ||| (y.setWidth 32).setWidth 64) = (x ++ y).setWidth 64 := by
  rw [BitVec.setWidth_setWidth (by decide), BitVec.setWidth_setWidth (by decide), bytes16]

theorem loadWord_run {r : Reg} (hr : r ≠ .x7) (hr₁ : r ≠ .x1) (k : Nat) (hk : k < 4) (s : State)
    {a : Addr} (ha : s.gpr .x1 = a) (hb : BlockRead s a) :
    ∃ s', runBlock isa (loadWord r k) s = some s' ∧
      s'.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++ s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      Keep [.x7, r] s s' := by
  have h0 := hb (2 * k) (by omega)
  have h1 := hb (2 * k + 1) (by omega)
  simp only [loadWord, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, isa,
    State.read, Size.bits, Nat.mod_one, show 2 * k < 4096 * 1 by omega,
    show 2 * k + 1 < 4096 * 1 by omega, and_self, ↓reduceIte, Option.bind_some, Option.map_some,
    ha, h0, h1, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hr,
    hr₁.symm, Nat.reduceLT, BitVec.setWidth_eq, read_one, Option.some.injEq,
    exists_eq_left']
  refine ⟨bytes16' _ _, ?_⟩
  keep_tac

theorem load_run (s : State) {a : Addr} (ha : s.gpr .x1 = a) (hb : BlockRead s a) :
    ∃ s', runBlock isa load s = some s' ∧
      Holds (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem a)) s' ∧
      Keep [.x3, .x4, .x5, .x6, .x7] s s' := by
  have w (k : Nat) (hk : k < 4) := decodeBlock_blockAt s.mem a hk
  obtain ⟨s₁, h₁, v₁, e₁⟩ := loadWord_run (r := .x3) (by decide) (by decide) 0 (by decide) s ha hb
  obtain ⟨s₂, h₂, v₂, e₂⟩ := loadWord_run (r := .x4) (by decide) (by decide) 1 (by decide) s₁
    ((e₁.reg .x1 (by decide)).trans ha) (hb.keep e₁)
  obtain ⟨s₃, h₃, v₃, e₃⟩ := loadWord_run (r := .x5) (by decide) (by decide) 2 (by decide) s₂
    ((e₂.reg .x1 (by decide)).trans ((e₁.reg .x1 (by decide)).trans ha)) ((hb.keep e₁).keep e₂)
  obtain ⟨s₄, h₄, v₄, e₄⟩ := loadWord_run (r := .x6) (by decide) (by decide) 3 (by decide) s₃
    ((e₃.reg .x1 (by decide)).trans ((e₂.reg .x1 (by decide)).trans ((e₁.reg .x1 (by decide)).trans ha)))
    (((hb.keep e₁).keep e₂).keep e₃)
  refine ⟨s₄, run_append (run_append (run_append h₁ h₂) h₃) h₄, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [e₄.reg .x3 (by decide), e₃.reg .x3 (by decide), e₂.reg .x3 (by decide), v₁, w 0 (by decide)]
  · rw [e₄.reg .x4 (by decide), e₃.reg .x4 (by decide), v₂, e₁.mem, w 1 (by decide)]
  · rw [e₄.reg .x5 (by decide), v₃, e₂.mem, e₁.mem, w 2 (by decide)]
  · rw [v₄, e₃.mem, e₂.mem, e₁.mem, w 3 (by decide)]
  · exact (e₁.mono (by decide)).trans ((e₂.mono (by decide)).trans ((e₃.mono (by decide)).trans
      (e₄.mono (by decide))))

/-! ## The rounds -/

theorem rounds_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) :
    ∀ n ≤ 8, ∀ s : State, Holds x s → KeyOk z s → MaskOk s →
      ∃ s', runBlock isa ((List.range n).flatMap round) s = some s' ∧
        Holds (roundsSpec z n x) s' ∧ Keep roundWrites s s'
  | 0, _, s, hx, _, _ => ⟨s, by simp [runBlock_nil], hx, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | n + 1, hn, s, hx, hk, hm => by
    obtain ⟨s₁, h₁, x₁, e₁⟩ := rounds_run z x n (by omega) s hx hk hm
    obtain ⟨s₂, h₂, x₂, e₂⟩ := round_run n (by omega) z _ s₁ x₁ (hk.keep e₁ (by decide))
      ((e₁.reg .x15 (by decide)).trans hm)
    refine ⟨s₂, ?_, ?_, e₁.trans e₂⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append h₁ h₂
    · simp only [roundsSpec, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact x₂

/-! ## The output transformation -/

/-- The output words: `Y₁` in `x3`, `Y₂` in `x5`, `Y₃` in `x4`, `Y₄` in `x6`. -/
structure OutHolds (y : Spec.Idea.State) (s : State) : Prop where
  x3 : s.gpr .x3 = (y.getD 0 0).setWidth 64
  x5 : s.gpr .x5 = (y.getD 1 0).setWidth 64
  x4 : s.gpr .x4 = (y.getD 2 0).setWidth 64
  x6 : s.gpr .x6 = (y.getD 3 0).setWidth 64

theorem ldr96_run (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 96) 8) :
    ∃ s', runBlock isa [.ldr .x .x8 .x0 96] s = some s' ∧
      s'.gpr .x8 = s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 96) 64 ∧ Keep [.x8] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, isa, Size.bytes,
    Size.bits, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ↓reduceIte, Option.bind_some,
    h, Option.map_some, RegUpd.gpr_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, by keep_tac⟩

theorem output_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x s)
    (hk : KeyOk z s) (hm : MaskOk s) :
    ∃ s', runBlock isa output s = some s' ∧
      OutHolds (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) x) s' ∧
      Keep roundWrites s s' := by
  obtain ⟨hl, hv⟩ := hk.last
  obtain ⟨s₁, h₁, v₁, e₁⟩ := ldr96_run s hl
  have m₁ : MaskOk s₁ := (e₁.reg .x15 (by decide)).trans hm
  have l0 := hv 0 (by decide)
  have l1 := hv 1 (by decide)
  have l2 := hv 2 (by decide)
  have l3 := hv 3 (by decide)
  simp only [Nat.mul_zero, BitVec.ushiftRight_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at l0 l1 l2 l3
  rw [← v₁] at l0 l1 l2 l3
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mul_run (d := .x3) .x3 (b := .x8) (by decide) s₁ m₁
  have m₂ : MaskOk s₂ := (e₂.reg .x15 (by decide)).trans m₁
  obtain ⟨s₃, h₃, v₃, e₃⟩ := lsr_run .x14 .x8 48 (by decide) s₂
  have m₃ : MaskOk s₃ := (e₃.reg .x15 (by decide)).trans m₂
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mul_run (d := .x6) .x6 (b := .x14) (by decide) s₃ m₃
  have m₄ : MaskOk s₄ := (e₄.reg .x15 (by decide)).trans m₃
  obtain ⟨s₅, h₅, v₅, e₅⟩ := lsr_run .x14 .x8 16 (by decide) s₄
  have m₅ : MaskOk s₅ := (e₅.reg .x15 (by decide)).trans m₄
  obtain ⟨s₆, h₆, v₆, e₆⟩ := addKey_run .x5 .x14 (by decide) s₅ m₅
  have m₆ : MaskOk s₆ := (e₆.reg .x15 (by decide)).trans m₅
  obtain ⟨s₇, h₇, v₇, e₇⟩ := lsr_run .x14 .x8 32 (by decide) s₆
  have m₇ : MaskOk s₇ := (e₇.reg .x15 (by decide)).trans m₆
  obtain ⟨s₈, h₈, v₈, e₈⟩ := addKey_run .x4 .x14 (by decide) s₇ m₇
  have x8₇ : s₆.gpr .x8 = s₁.gpr .x8 := by
    rw [e₆.reg .x8 (by decide), e₅.reg .x8 (by decide),
      e₄.reg .x8 (by decide), e₃.reg .x8 (by decide), e₂.reg .x8 (by decide)]
  have x8₅ : s₄.gpr .x8 = s₁.gpr .x8 := by
    rw [e₄.reg .x8 (by decide), e₃.reg .x8 (by decide), e₂.reg .x8 (by decide)]
  refine ⟨s₈, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [output]
    exact run_append (run_append (run_append (run_append (run_append (run_append (run_append h₁ h₂)
      h₃) h₄) h₅) h₆) h₇) h₈
  · rw [e₈.reg .x3 (by decide), e₇.reg .x3 (by decide), e₆.reg .x3 (by decide),
      e₅.reg .x3 (by decide), e₄.reg .x3 (by decide), e₃.reg .x3 (by decide), v₂,
      e₁.reg .x3 (by decide), hx.x3, setWidth_setWidth16, l0, output_getD0]
  · rw [e₈.reg .x5 (by decide), e₇.reg .x5 (by decide), v₆, v₅, x8₅, e₅.reg .x5 (by decide),
      e₄.reg .x5 (by decide), e₃.reg .x5 (by decide), e₂.reg .x5 (by decide),
      e₁.reg .x5 (by decide), hx.x5, add_mask, l1, output_getD1]
  · rw [v₈, v₇, x8₇, e₇.reg .x4 (by decide), e₆.reg .x4 (by decide), e₅.reg .x4 (by decide),
      e₄.reg .x4 (by decide), e₃.reg .x4 (by decide), e₂.reg .x4 (by decide),
      e₁.reg .x4 (by decide), hx.x4, add_mask, l2, output_getD2]
  · rw [e₈.reg .x6 (by decide), e₇.reg .x6 (by decide), e₆.reg .x6 (by decide),
      e₅.reg .x6 (by decide), v₄, v₃, e₃.reg .x6 (by decide), e₂.reg .x6 (by decide),
      e₁.reg .x6 (by decide), hx.x6, setWidth_setWidth16, e₂.reg .x8 (by decide), l3, output_getD3]
  · exact ((((((((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans
      (e₃.weaken (by decide))).trans (e₄.weaken (by decide))).trans (e₅.weaken (by decide))).trans
      (e₆.weaken (by decide))).trans (e₇.weaken (by decide))).trans (e₈.weaken (by decide)))

/-! ## Storing -/

/-- `strb t, [n, #off]` first in a block: memory alone changes. -/
theorem strb_cons {s : State} {t n : Reg} {off : Nat} {a : Addr} {is : List Instr} (ho : off < 4096)
    (ha : s.gpr n = a) (h : InRegions s.wr (a + BitVec.ofNat 64 off) 1) :
    runBlock isa (.strb t n off :: is) s =
      runBlock isa is { s with mem := s.mem.write (a + BitVec.ofNat 64 off) 1 ((s.gpr t).setWidth 8) } := by
  rw [runBlock_cons, ← runStep_some]
  congr 1
  subst ha
  simp only [exec, addr, Nat.mod_one, show off < 4096 * 1 from ho, and_self, ↓reduceIte,
    Option.bind_some, State.store, h, State.read, Size.bits,
    BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]

theorem storeWord_run (r : Reg) (k : Nat) (hk : k < 4) (s : State) {a : Addr}
    (ha : s.gpr .x1 = a)
    (h1 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k + 1)) 1)
    (h0 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k)) 1) :
    ∃ s', runBlock isa (storeWord r k) s = some s' ∧
      s'.mem = (s.mem.write (a + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r).setWidth 8)).write
        (a + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r >>> 8).setWidth 8) ∧
      (∀ q, q ≠ .x14 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨?w, ?run, ?_, ?_, ?_, ?_, ?_⟩
  case run =>
    rw [storeWord, strb_cons (by omega) ha h1, runBlock_cons, exec_lsr_x (by decide), runStep_some,
      strb_cons (a := a) (by omega) ?_ ?_, runBlock_nil]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ↓reduceIte]
      exact ha
    · exact h0
  · rfl
  · intro q hq
    simp only [RegUpd.gpr_write, hq, ↓reduceIte]
  all_goals rfl

/-- The bytes of the block at `a` can be written. -/
def BlockWrite (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions s.wr (a + BitVec.ofNat 64 i) 1

theorem frame_write1 {a : Addr} {m m' : Mem} {j : Nat} (v : BitVec 8) (hj : j < 8)
    (h : Frame [⟨a, 8⟩] m m') : Frame [⟨a, 8⟩] m (m'.write (a + BitVec.ofNat 64 j) 1 v) :=
  h.write (List.mem_singleton_self _) (n := 1) v (Offset.contains_base a (by omega) (by omega))

theorem store_run (y : Spec.Idea.State) (s : State) {a : Addr} (ha : s.gpr .x1 = a)
    (hw : BlockWrite s a) (hy : OutHolds y s) :
    ∃ s', runBlock isa store s = some s' ∧
      Spec.Idea.blockAt s'.mem a = Spec.Idea.encodeBlock y ∧
      Frame [⟨a, 8⟩] s.mem s'.mem ∧ (∀ q, q ≠ .x14 → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, h₁, m₁, g₁, rd₁, wr₁, sp₁⟩ :=
    storeWord_run .x3 0 (by decide) s ha (hw _ (by decide)) (hw _ (by decide))
  have ha₁ : s₁.gpr .x1 = a := (g₁ .x1 (by decide)).trans ha
  have hw₁ : BlockWrite s₁ a := fun i hi => wr₁ ▸ hw i hi
  obtain ⟨s₂, h₂, m₂, g₂, rd₂, wr₂, sp₂⟩ :=
    storeWord_run .x5 1 (by decide) s₁ ha₁ (hw₁ _ (by decide)) (hw₁ _ (by decide))
  have ha₂ : s₂.gpr .x1 = a := (g₂ .x1 (by decide)).trans ha₁
  have hw₂ : BlockWrite s₂ a := fun i hi => wr₂ ▸ hw₁ i hi
  obtain ⟨s₃, h₃, m₃, g₃, rd₃, wr₃, sp₃⟩ :=
    storeWord_run .x4 2 (by decide) s₂ ha₂ (hw₂ _ (by decide)) (hw₂ _ (by decide))
  have ha₃ : s₃.gpr .x1 = a := (g₃ .x1 (by decide)).trans ha₂
  have hw₃ : BlockWrite s₃ a := fun i hi => wr₃ ▸ hw₂ i hi
  obtain ⟨s₄, h₄, m₄, g₄, rd₄, wr₄, sp₄⟩ :=
    storeWord_run .x6 3 (by decide) s₃ ha₃ (hw₃ _ (by decide)) (hw₃ _ (by decide))
  have v5 : s₁.gpr .x5 = (y.getD 1 0).setWidth 64 := (g₁ .x5 (by decide)).trans hy.x5
  have v4 : s₂.gpr .x4 = (y.getD 2 0).setWidth 64 :=
    (g₂ .x4 (by decide)).trans ((g₁ .x4 (by decide)).trans hy.x4)
  have v6 : s₃.gpr .x6 = (y.getD 3 0).setWidth 64 :=
    (g₃ .x6 (by decide)).trans ((g₂ .x6 (by decide)).trans ((g₁ .x6 (by decide)).trans hy.x6))
  rw [v6] at m₄
  rw [v4] at m₃
  rw [v5] at m₂
  rw [hy.x3] at m₁
  rw [m₃, m₂, m₁] at m₄
  refine ⟨s₄, run_append (run_append (run_append h₁ h₂) h₃) h₄, ?_, ?_,
    fun q hq => (g₄ q hq).trans ((g₃ q hq).trans ((g₂ q hq).trans (g₁ q hq))),
    rd₄.trans (rd₃.trans (rd₂.trans rd₁)), wr₄.trans (wr₃.trans (wr₂.trans wr₁)),
    sp₄.trans (sp₃.trans (sp₂.trans sp₁))⟩
  · apply Vector.ext
    intro i hi
    simp only [Spec.Idea.blockAt, Vector.getElem_ofFn, m₄, encodeBlock_get _ hi]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
        i = 5 ∨ i = 6 ∨ i = 7 := by omega
    all_goals simp (disch := decide) only [write1_apply, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte, lo8, hi8, BitVec.ushiftRight_zero]
  · rw [m₄]
    repeat' apply frame_write1 _ (by decide)
    exact Frame.refl _ _

/-! ## A block -/

theorem cryptBlock_run (z : Spec.Idea.Schedule) (s : State) {a : Addr} (ha : s.gpr .x1 = a)
    (hb : BlockRead s a) (hw : BlockWrite s a) (hk : KeyOk z s) (hm : MaskOk s) :
    ∃ s', runBlock isa cryptBlock s = some s' ∧
      Spec.Idea.blockAt s'.mem a = Spec.Idea.cryptBlock z (Spec.Idea.blockAt s.mem a) ∧
      Frame [⟨a, 8⟩] s.mem s'.mem ∧ (∀ q, q ∉ roundWrites → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, h₁, x₁, e₁⟩ := load_run s ha hb
  have k₁ := hk.keep e₁ (by decide)
  have m₁ : MaskOk s₁ := (e₁.reg .x15 (by decide)).trans hm
  obtain ⟨s₂, h₂, x₂, e₂⟩ := rounds_run z _ 8 (by decide) s₁ x₁ k₁ m₁
  obtain ⟨s₃, h₃, x₃, e₃⟩ := output_run z _ s₂ x₂ (k₁.keep e₂ (by decide))
    ((e₂.reg .x15 (by decide)).trans m₁)
  have e₁₃ := ((e₁.weaken (by decide)).trans e₂).trans e₃
  obtain ⟨s₄, h₄, b₄, f₄, g₄, rd₄, wr₄, sp₄⟩ := store_run _ s₃ ((e₁₃.reg .x1 (by decide)).trans ha)
    (fun i hi => e₁₃.wr ▸ hw i hi) x₃
  refine ⟨s₄, ?_, ?_, ?_, fun q hq => ?_, rd₄.trans e₁₃.rd, wr₄.trans e₁₃.wr, sp₄.trans e₁₃.sp⟩
  · simp only [cryptBlock]
    exact run_append (run_append (run_append h₁ h₂) h₃) h₄
  · rw [b₄, Spec.Idea.cryptBlock, crypt_eq]
  · rw [← e₁₃.mem]; exact f₄
  · rw [g₄ q (by intro h; subst h; exact hq (by decide)), e₁₃.reg q hq]

end VG.Proof.Idea.AArch64
