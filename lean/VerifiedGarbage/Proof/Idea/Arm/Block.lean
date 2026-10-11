import VerifiedGarbage.Proof.Idea.Arm.Round

/-!
# IDEA on ARMv7: a block

`cryptBlock_run`: `Impl.Idea.Arm.cryptBlock` replaces the block at `r1` with
`Spec.Idea.cryptBlock` of it under the subkeys at `r0`, writing no register
but `r4`–`r12`: the interface a mode reuses it through.
-/

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Impl.Idea.Arm

/-- The block at `r1` (64-bit address `A`, not wrapping around). -/
structure BlockAt (s : State) (A : Addr) : Prop where
  addr : State.addr (s.gpr .r1) = A
  fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32

theorem BlockAt.keep {rs : List Reg} {s s' : State} {A : Addr} (h : BlockAt s A)
    (hk : Keep rs s s') (hr1 : .r1 ∉ rs) : BlockAt s' A :=
  ⟨by rw [hk.reg .r1 hr1]; exact h.addr, by rw [hk.reg .r1 hr1]; exact h.fit⟩

theorem BlockAt.off {s : State} {A : Addr} (h : BlockAt s A) {k : Nat} (hk : k < 8) :
    State.addr (s.gpr .r1 + BitVec.ofNat 32 k) = A + BitVec.ofNat 64 k := by
  rw [addr_add (by have := h.fit; omega), h.addr]

/-- The bytes of the block at `A` can be read. -/
def BlockRead (s : State) (A : Addr) : Prop :=
  ∀ i < 8, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 i) 1

/-- The bytes of the block at `A` can be written. -/
def BlockWrite (s : State) (A : Addr) : Prop :=
  ∀ i < 8, InRegions s.wr (A + BitVec.ofNat 64 i) 1

/-! ## Loading -/

theorem loadWord_run {r : Reg} (hr : r ≠ .r8) (hr₁ : r ≠ .r1) (k : Nat) (hk : k < 4) (s : State)
    {A : Addr} (ha : BlockAt s A) (hb : BlockRead s A) :
    ∃ s', runBlock isa (loadWord r k) s = some s' ∧
      s'.gpr r = (s.mem (A + BitVec.ofNat 64 (2 * k)) ++ s.mem (A + BitVec.ofNat 64 (2 * k + 1))).setWidth 32 ∧
      Keep [.r8, r] s s' := by
  have h0 := hb (2 * k) (by omega)
  have h1 := hb (2 * k + 1) (by omega)
  simp only [loadWord, runBlock_cons, runStep_some, runBlock_nil, isa, exec, State.load8, Op2.eval,
    show 2 * k < 4096 by omega, show 2 * k + 1 < 4096 by omega, ↓reduceIte,
    ha.off (k := 2 * k) (by omega), ha.off (k := 2 * k + 1) (by omega), h0, h1,
    Option.map_some, RegUpd.gpr_setReg, hr, hr₁.symm, Nat.reduceLeDiff, and_self,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, Option.some.injEq, exists_eq_left']
  refine ⟨bytes16_32 _ _, ?_⟩
  keep_tac

theorem load_run (s : State) {A : Addr} (ha : BlockAt s A) (hb : BlockRead s A) :
    ∃ s', runBlock isa load s = some s' ∧
      Holds (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)) .r5 .r6 s' ∧
      Keep [.r4, .r5, .r6, .r7, .r8] s s' := by
  have w (k : Nat) (hk : k < 4) := decodeBlock_blockAt s.mem A hk
  obtain ⟨s₁, h₁, v₁, e₁⟩ := loadWord_run (r := .r4) (by decide) (by decide) 0 (by decide) s ha hb
  have hb₁ : BlockRead s₁ A := fun i hi => by rw [e₁.rd, e₁.wr]; exact hb i hi
  obtain ⟨s₂, h₂, v₂, e₂⟩ := loadWord_run (r := .r5) (by decide) (by decide) 1 (by decide) s₁
    (ha.keep e₁ (by decide)) hb₁
  have hb₂ : BlockRead s₂ A := fun i hi => by rw [e₂.rd, e₂.wr]; exact hb₁ i hi
  obtain ⟨s₃, h₃, v₃, e₃⟩ := loadWord_run (r := .r6) (by decide) (by decide) 2 (by decide) s₂
    ((ha.keep e₁ (by decide)).keep e₂ (by decide)) hb₂
  have hb₃ : BlockRead s₃ A := fun i hi => by rw [e₃.rd, e₃.wr]; exact hb₂ i hi
  obtain ⟨s₄, h₄, v₄, e₄⟩ := loadWord_run (r := .r7) (by decide) (by decide) 3 (by decide) s₃
    (((ha.keep e₁ (by decide)).keep e₂ (by decide)).keep e₃ (by decide)) hb₃
  refine ⟨s₄, run_append (run_append (run_append h₁ h₂) h₃) h₄, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [e₄.reg .r4 (by decide), e₃.reg .r4 (by decide), e₂.reg .r4 (by decide), v₁, w 0 (by decide)]
  · rw [e₄.reg .r5 (by decide), e₃.reg .r5 (by decide), v₂, e₁.mem, w 1 (by decide)]
  · rw [e₄.reg .r6 (by decide), v₃, e₂.mem, e₁.mem, w 2 (by decide)]
  · rw [v₄, e₃.mem, e₂.mem, e₁.mem, w 3 (by decide)]
  · exact (e₁.weaken (by decide)).trans ((e₂.weaken (by decide)).trans ((e₃.weaken (by decide)).trans
      (e₄.weaken (by decide))))

/-! ## The rounds -/

theorem regB_succ (n : Nat) : regB (n + 1) = regC n := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h, show (n + 1) % 2 = 0 ↔ ¬ n % 2 = 0 by omega]

theorem regC_succ (n : Nat) : regC (n + 1) = regB n := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h, show (n + 1) % 2 = 0 ↔ ¬ n % 2 = 0 by omega]

theorem regBC_ok (n : Nat) : (regB n == .r5 && regC n == .r6 || regB n == .r6 && regC n == .r5) = true := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h]

theorem rounds_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) :
    ∀ n ≤ 8, ∀ s : State, Holds x .r5 .r6 s → KeyOk z s → MaskOk s →
      ∃ s', runBlock isa ((List.range n).flatMap round) s = some s' ∧
        Holds (roundsSpec z n x) (regB n) (regC n) s' ∧ Keep roundWrites s s'
  | 0, _, s, hx, _, _ => ⟨s, by simp [runBlock_nil], hx, Keep.refl _ _⟩
  | n + 1, hn, s, hx, hk, hm => by
    obtain ⟨s₁, h₁, x₁, e₁⟩ := rounds_run z x n (by omega) s hx hk hm
    obtain ⟨s₂, h₂, x₂, e₂⟩ := round_run n (by omega) (regB n) (regC n) (regBC_ok n) z _ s₁ x₁
      (hk.keep e₁ (by decide)) ((e₁.reg .r12 (by decide)).trans hm)
    refine ⟨s₂, ?_, ?_, e₁.trans e₂⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append h₁ h₂
    · simp only [roundsSpec, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        regB_succ, regC_succ]
      exact x₂

/-! ## The output transformation -/

/-- The output words: `Y₁` in `r4`, `Y₂` in `r6`, `Y₃` in `r5`, `Y₄` in `r7`. -/
structure OutHolds (y : Spec.Idea.State) (s : State) : Prop where
  r4 : s.gpr .r4 = (y.getD 0 0).setWidth 32
  r6 : s.gpr .r6 = (y.getD 1 0).setWidth 32
  r5 : s.gpr .r5 = (y.getD 2 0).setWidth 32
  r7 : s.gpr .r7 = (y.getD 3 0).setWidth 32

theorem output_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x .r5 .r6 s)
    (hk : KeyOk z s) (hm : MaskOk s) :
    ∃ s', runBlock isa output s = some s' ∧
      OutHolds (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) x) s' ∧
      Keep roundWrites s s' := by
  obtain ⟨s₁, h₁, v₁, e₁⟩ := loadKey_run .r9 48 (by decide) s hk
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mul_run .r4 .r4 .r9 (by decide) s₁ ((e₁.reg .r12 (by decide)).trans hm)
  have e₂' : Keep [.r4, .r8, .r9] s s₂ := (e₁.weaken (by decide)).trans (e₂.weaken (by decide))
  obtain ⟨s₃, h₃, v₃, e₃⟩ := loadKey_run .r9 51 (by decide) s₂ (hk.keep e₂' (by decide))
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mul_run .r7 .r7 .r9 (by decide) s₃
    ((e₃.reg .r12 (by decide)).trans ((e₂'.reg .r12 (by decide)).trans hm))
  have e₄' : Keep [.r4, .r7, .r8, .r9] s s₄ :=
    ((e₂'.weaken (by decide)).trans (e₃.weaken (by decide))).trans (e₄.weaken (by decide))
  obtain ⟨s₅, h₅, v₅, e₅⟩ := loadKey_run .r9 49 (by decide) s₄ (hk.keep e₄' (by decide))
  obtain ⟨s₆, h₆, v₆, e₆⟩ := addKey_run .r6 (by decide) s₅
    ((e₅.reg .r12 (by decide)).trans ((e₄'.reg .r12 (by decide)).trans hm))
  have e₆' : Keep [.r4, .r6, .r7, .r8, .r9] s s₆ :=
    ((e₄'.weaken (by decide)).trans (e₅.weaken (by decide))).trans (e₆.weaken (by decide))
  obtain ⟨s₇, h₇, v₇, e₇⟩ := loadKey_run .r9 50 (by decide) s₆ (hk.keep e₆' (by decide))
  obtain ⟨s₈, h₈, v₈, e₈⟩ := addKey_run .r5 (by decide) s₇
    ((e₇.reg .r12 (by decide)).trans ((e₆'.reg .r12 (by decide)).trans hm))
  refine ⟨s₈, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact run_append (run_append (run_append (run_append (run_append (run_append (run_append h₁ h₂)
      h₃) h₄) h₅) h₆) h₇) h₈
  · rw [e₈.reg .r4 (by decide), e₇.reg .r4 (by decide), e₆.reg .r4 (by decide), e₅.reg .r4 (by decide), e₄.reg .r4 (by decide), e₃.reg .r4 (by decide),
      v₂, e₁.reg .r4 (by decide), hx.r4, setWidth_setWidth16_32, v₁]
    rfl
  · rw [e₈.reg .r6 (by decide), e₇.reg .r6 (by decide), v₆, e₅.reg .r6 (by decide),
      e₄'.reg .r6 (by decide), hx.c, add_mask32, v₅]
    rfl
  · rw [v₈, e₇.reg .r5 (by decide), e₆'.reg .r5 (by decide), hx.b, add_mask32, v₇]
    rfl
  · rw [e₈.reg .r7 (by decide), e₇.reg .r7 (by decide), e₆.reg .r7 (by decide), e₅.reg .r7 (by decide),
      v₄, v₃, e₃.reg .r7 (by decide), e₂'.reg .r7 (by decide), hx.r7, setWidth_setWidth16_32]
    rfl
  · exact (((e₆'.weaken (by decide)).trans (e₇.weaken (by decide))).trans (e₈.weaken (by decide)))

/-! ## Storing -/

theorem storeWord_run (r : Reg) (k : Nat) (hk : k < 4) (s : State) {A : Addr}
    (ha : BlockAt s A) (hw : BlockWrite s A) :
    ∃ s', runBlock isa (storeWord r k) s = some s' ∧
      s'.mem = (s.mem.writeW (A + BitVec.ofNat 64 (2 * k + 1)) ((s.gpr r).setWidth 8)).writeW
        (A + BitVec.ofNat 64 (2 * k)) ((s.gpr r >>> 8).setWidth 8) ∧
      (∀ q, q ≠ .r8 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h0 := hw (2 * k) (by omega)
  have h1 := hw (2 * k + 1) (by omega)
  simp only [storeWord, runBlock_cons, runStep_some, runBlock_nil, isa, exec, State.store8, Op2.eval,
    show 2 * k < 4096 by omega, show 2 * k + 1 < 4096 by omega, ↓reduceIte, h0, h1,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, Nat.reduceLeDiff, and_self,
    reduceCtorEq, ha.off (k := 2 * k) (by omega), ha.off (k := 2 * k + 1) (by omega),
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q hq => ite_eq_right hq, rfl, trivial, rfl⟩

theorem frame_write8 {a : Addr} {m m' : Mem} {j : Nat} (v : BitVec 8) (hj : j < 8)
    (h : Frame [⟨a, 8⟩] m m') : Frame [⟨a, 8⟩] m (m'.writeW (a + BitVec.ofNat 64 j) v) :=
  h.writeW (List.mem_singleton_self _) v (Offset.contains_base a (by omega) (by omega))

/-- What a store keeps. -/
structure StoreKeep (s s' : State) : Prop where
  reg : ∀ q, q ≠ .r8 → s'.gpr q = s.gpr q
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem StoreKeep.trans {s s' s'' : State} (h : StoreKeep s s') (h' : StoreKeep s' s'') :
    StoreKeep s s'' :=
  ⟨fun q hq => (h'.reg q hq).trans (h.reg q hq), h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem store_run (y : Spec.Idea.State) (s : State) {A : Addr} (ha : BlockAt s A)
    (hw : BlockWrite s A) (hy : OutHolds y s) :
    ∃ s', runBlock isa store s = some s' ∧
      Spec.Idea.blockAt s'.mem A = Spec.Idea.encodeBlock y ∧
      Frame [⟨A, 8⟩] s.mem s'.mem ∧ StoreKeep s s' := by
  have step : ∀ (r : Reg) (k : Nat), k < 4 → ∀ t : State, BlockAt t A → BlockWrite t A →
      ∃ t', runBlock isa (storeWord r k) t = some t' ∧
        t'.mem = (t.mem.writeW (A + BitVec.ofNat 64 (2 * k + 1)) ((t.gpr r).setWidth 8)).writeW
          (A + BitVec.ofNat 64 (2 * k)) ((t.gpr r >>> 8).setWidth 8) ∧
        StoreKeep t t' ∧ BlockAt t' A ∧ BlockWrite t' A := by
    intro r k hk t hat hwt
    obtain ⟨t', h, m, g, rd, wr, sp⟩ := storeWord_run r k hk t hat hwt
    exact ⟨t', h, m, ⟨g, rd, wr, sp⟩, ⟨by rw [g .r1 (by decide)]; exact hat.addr,
      by rw [g .r1 (by decide)]; exact hat.fit⟩, fun i hi => by rw [wr]; exact hwt i hi⟩
  obtain ⟨s₁, h₁, m₁, k₁, a₁, w₁⟩ := step .r4 0 (by decide) s ha hw
  obtain ⟨s₂, h₂, m₂, k₂, a₂, w₂⟩ := step .r6 1 (by decide) s₁ a₁ w₁
  obtain ⟨s₃, h₃, m₃, k₃, a₃, w₃⟩ := step .r5 2 (by decide) s₂ a₂ w₂
  obtain ⟨s₄, h₄, m₄, k₄, -, -⟩ := step .r7 3 (by decide) s₃ a₃ w₃
  have v6 : s₁.gpr .r6 = (y.getD 1 0).setWidth 32 := (k₁.reg .r6 (by decide)).trans hy.r6
  have v5 : s₂.gpr .r5 = (y.getD 2 0).setWidth 32 :=
    (k₂.reg .r5 (by decide)).trans ((k₁.reg .r5 (by decide)).trans hy.r5)
  have v7 : s₃.gpr .r7 = (y.getD 3 0).setWidth 32 :=
    (k₃.reg .r7 (by decide)).trans ((k₂.reg .r7 (by decide)).trans ((k₁.reg .r7 (by decide)).trans hy.r7))
  rw [v7] at m₄
  rw [v5] at m₃
  rw [v6] at m₂
  rw [hy.r4] at m₁
  rw [m₃, m₂, m₁] at m₄
  refine ⟨s₄, run_append (run_append (run_append h₁ h₂) h₃) h₄, ?_, ?_, ((k₁.trans k₂).trans k₃).trans k₄⟩
  · apply Vector.ext
    intro i hi
    simp only [Spec.Idea.blockAt, Vector.getElem_ofFn, m₄, encodeBlock_get _ hi]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
        i = 5 ∨ i = 6 ∨ i = 7 := by omega
    all_goals simp (disch := decide) only [write8_apply, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte, lo8_32, hi8_32, BitVec.ushiftRight_zero]
  · rw [m₄]
    repeat' apply frame_write8 _ (by decide)
    exact Frame.refl _ _

/-! ## A block -/

/-- The registers `cryptBlock` writes. -/
abbrev blockWrites : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem setMask_run (s : State) :
    ∃ s', runBlock isa [setMask] s = some s' ∧ MaskOk s' ∧ Keep [.r12] s s' := by
  simp only [setMask, runBlock_cons, runStep_some, runBlock_nil, isa, exec, Option.some.injEq,
    exists_eq_left']
  exact ⟨rfl, by keep_tac⟩

theorem cryptBlock_run (z : Spec.Idea.Schedule) (s : State) {A : Addr} (ha : BlockAt s A)
    (hb : BlockRead s A) (hw : BlockWrite s A) (hk : KeyOk z s) :
    ∃ s', runBlock isa cryptBlock s = some s' ∧
      Spec.Idea.blockAt s'.mem A = Spec.Idea.cryptBlock z (Spec.Idea.blockAt s.mem A) ∧
      Frame [⟨A, 8⟩] s.mem s'.mem ∧ (∀ q, q ∉ blockWrites → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₀, h₀, m₀, e₀⟩ := setMask_run s
  have hb₀ : BlockRead s₀ A := fun i hi => by rw [e₀.rd, e₀.wr]; exact hb i hi
  obtain ⟨s₁, h₁, x₁, e₁⟩ := load_run s₀ (ha.keep e₀ (by decide)) hb₀
  have e₀₁ : Keep blockWrites s s₁ := (e₀.weaken (by decide)).trans (e₁.weaken (by decide))
  have k₁ := hk.keep e₀₁ (by decide)
  have m₁ : MaskOk s₁ := (e₁.reg .r12 (by decide)).trans m₀
  obtain ⟨s₂, h₂, x₂, e₂⟩ := rounds_run z _ 8 (by decide) s₁ x₁ k₁ m₁
  obtain ⟨s₃, h₃, x₃, e₃⟩ := output_run z _ s₂ x₂ (k₁.keep e₂ (by decide))
    ((e₂.reg .r12 (by decide)).trans m₁)
  have e₁₃ : Keep blockWrites s s₃ := (e₀₁.trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))
  obtain ⟨s₄, h₄, b₄, f₄, k₄⟩ := store_run _ s₃ (ha.keep e₁₃ (by decide))
    (fun i hi => e₁₃.wr ▸ hw i hi) x₃
  refine ⟨s₄, ?_, ?_, ?_, fun q hq => ?_, k₄.rd.trans e₁₃.rd, k₄.wr.trans e₁₃.wr, k₄.sp.trans e₁₃.sp⟩
  · exact run_append (a := [setMask]) h₀ (run_append (run_append (run_append h₁ h₂) h₃) h₄)
  · rw [b₄, Spec.Idea.cryptBlock, crypt_eq, e₀.mem]
  · rw [← e₁₃.mem]; exact f₄
  · rw [k₄.reg q (by intro h; subst h; exact hq (by decide)), e₁₃.reg q hq]

end VG.Proof.Idea.Arm
