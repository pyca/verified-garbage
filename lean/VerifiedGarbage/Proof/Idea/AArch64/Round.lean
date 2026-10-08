import VerifiedGarbage.Proof.Idea.AArch64.Mul

/-!
# IDEA on AArch64: a round

`round_run`: round `j` of the code maps the state words in `x3`–`x6`
(`Holds`) to `Spec.Idea.round` of them under subkeys `6j … 6j + 5`, loaded
two at a time from the schedule at `x0` (`KeyOk`).
-/

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.Impl.Idea.AArch64

/-- The state words are in `x3`–`x6`, zero-extended. -/
structure Holds (x : Spec.Idea.State) (s : State) : Prop where
  x3 : s.gpr .x3 = (x.getD 0 0).setWidth 64
  x4 : s.gpr .x4 = (x.getD 1 0).setWidth 64
  x5 : s.gpr .x5 = (x.getD 2 0).setWidth 64
  x6 : s.gpr .x6 = (x.getD 3 0).setWidth 64

/-- The schedule `z` is at `x0`, readable. -/
structure KeyOk (z : Spec.Idea.Schedule) (s : State) : Prop where
  read : ⟨s.gpr .x0, 104⟩ ∈ s.rd ++ s.wr
  sched : Spec.Idea.scheduleAt s.mem (s.gpr .x0) = z

theorem KeyOk.keep {z : Spec.Idea.Schedule} {rs : List Reg} {s s' : State} (h : KeyOk z s)
    (hk : Keep rs s s') (hx0 : .x0 ∉ rs) : KeyOk z s' := by
  refine ⟨?_, ?_⟩
  · rw [hk.rd, hk.wr, hk.reg .x0 hx0]; exact h.read
  · rw [hk.mem, hk.reg .x0 hx0]; exact h.sched

/-- Subkeys `2k` and `2k + 1`, at `x0 + 4k`. -/
theorem KeyOk.pair {z : Spec.Idea.Schedule} {s : State} (h : KeyOk z s) {k : Nat} (hk : k < 26) :
    InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 ∧
      ((s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 32).setWidth 64).setWidth 16 =
        z.getD (2 * k) 0 ∧
      (((s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 32).setWidth 64) >>> 16).setWidth 16 =
        z.getD (2 * k + 1) 0 := by
  refine ⟨⟨_, h.read, Offset.contains_base _ (by omega) (by omega)⟩, ?_, ?_⟩
  · have e := subkey_read32 s.mem (s.gpr .x0) hk (h := 0) (by decide)
    rw [Nat.mul_zero, BitVec.ushiftRight_zero, Nat.add_zero, h.sched] at e
    exact e
  · have e := subkey_read32 s.mem (s.gpr .x0) hk (h := 1) (by decide)
    rw [Nat.mul_one, h.sched] at e
    exact e

/-- Subkeys `48 + j`, the words of the quadword at `x0 + 96`. -/
theorem KeyOk.last {z : Spec.Idea.Schedule} {s : State} (h : KeyOk z s) :
    InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 96) 8 ∧
      ∀ j < 4, ((s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 96) 64) >>> (16 * j)).setWidth 16 =
        z.getD (48 + j) 0 :=
  ⟨⟨_, h.read, Offset.contains_base _ (by decide) (by decide)⟩, fun j hj => by
    rw [subkey_read96 _ _ hj, h.sched]⟩

macro "keep_tac" : tactic => `(tactic| (
  refine keep_reg_of (fun q hq => ?_) rfl rfl rfl rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_write, hq, ite_false]))

theorem loads_run (s : State) (j : Nat) (hj : j < 8) (z : Spec.Idea.Schedule) (hk : KeyOk z s) :
    ∃ s', runBlock isa [.ldr .w .x8 .x0 (12 * j), .ldr .w .x9 .x0 (12 * j + 4),
        .ldr .w .x13 .x0 (12 * j + 8)] s = some s' ∧
      (s'.gpr .x8).setWidth 16 = z.getD (6 * j) 0 ∧
      ((s'.gpr .x8) >>> 16).setWidth 16 = z.getD (6 * j + 1) 0 ∧
      (s'.gpr .x9).setWidth 16 = z.getD (6 * j + 2) 0 ∧
      ((s'.gpr .x9) >>> 16).setWidth 16 = z.getD (6 * j + 3) 0 ∧
      (s'.gpr .x13).setWidth 16 = z.getD (6 * j + 4) 0 ∧
      ((s'.gpr .x13) >>> 16).setWidth 16 = z.getD (6 * j + 5) 0 ∧
      Keep [.x8, .x9, .x13] s s' := by
  have p₀ := hk.pair (k := 3 * j) (by omega)
  have p₁ := hk.pair (k := 3 * j + 1) (by omega)
  have p₂ := hk.pair (k := 3 * j + 2) (by omega)
  rw [show 4 * (3 * j) = 12 * j by omega, show 2 * (3 * j) + 1 = 6 * j + 1 by omega,
    show 2 * (3 * j) = 6 * j by omega] at p₀
  rw [show 4 * (3 * j + 1) = 12 * j + 4 by omega, show 2 * (3 * j + 1) + 1 = 6 * j + 3 by omega,
    show 2 * (3 * j + 1) = 6 * j + 2 by omega] at p₁
  rw [show 4 * (3 * j + 2) = 12 * j + 8 by omega, show 2 * (3 * j + 2) + 1 = 6 * j + 5 by omega,
    show 2 * (3 * j + 2) = 6 * j + 4 by omega] at p₂
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, isa, Size.bytes,
    show (12 * j) % 4 = 0 by omega, show 12 * j < 4096 * 4 by omega,
    show (12 * j + 4) % 4 = 0 by omega, show 12 * j + 4 < 4096 * 4 by omega,
    show (12 * j + 8) % 4 = 0 by omega, show 12 * j + 8 < 4096 * 4 by omega, and_self, ↓reduceIte,
    Option.bind_some, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    reduceCtorEq, p₀.1, p₁.1, p₂.1, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨p₀.2.1, p₀.2.2, p₁.2.1, p₁.2.2, p₂.2.1, p₂.2.2, ?_⟩
  keep_tac

theorem lsr_run (d n : Reg) (sh : Nat) (hsh : sh < 64) (s : State) :
    ∃ s', runBlock isa [.lsr .x d n sh] s = some s' ∧ s'.gpr d = s.gpr n >>> sh ∧ Keep [d] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits, hsh,
    ↓reduceIte, BitVec.setWidth_eq, RegUpd.gpr_write, Option.some.injEq, exists_eq_left', true_and]
  keep_tac

theorem addKey_run (r k : Reg) (hr : r ≠ .x15) (s : State) (hm : MaskOk s) :
    ∃ s', runBlock isa (addKey r k) s = some s' ∧
      s'.gpr r = (s.gpr r + s.gpr k) &&& 65535 ∧ Keep [r] s s' := by
  simp only [addKey, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, ↓reduceIte, Ne.symm hr, hm, Option.some.injEq,
    exists_eq_left', true_and]
  keep_tac

theorem mid_run (s : State) :
    ∃ s', runBlock isa [.logic .eor .x .x14 .x4 .x6, .add .x .x14 .x14 .x7, .lsr .x .x10 .x13 16] s =
        some s' ∧
      s'.gpr .x14 = (s.gpr .x4 ^^^ s.gpr .x6) + s.gpr .x7 ∧ s'.gpr .x10 = s.gpr .x13 >>> 16 ∧
      Keep [.x14, .x10] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, Nat.reduceLT,
    Option.some.injEq, exists_eq_left', true_and]
  keep_tac

theorem eor_run (d n m : Reg) (s : State) :
    ∃ s', runBlock isa [.logic .eor .x d n m] s = some s' ∧ s'.gpr d = s.gpr n ^^^ s.gpr m ∧
      Keep [d] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, ↓reduceIte, Option.some.injEq, exists_eq_left', true_and]
  keep_tac

theorem tail_run (s : State) (hm : MaskOk s) :
    ∃ s', runBlock isa [.add .x .x7 .x7 .x14, .logic .and .x .x7 .x7 .x15,
        .logic .eor .x .x3 .x3 .x14, .logic .eor .x .x5 .x5 .x14,
        .logic .eor .x .x4 .x4 .x7, .logic .eor .x .x6 .x6 .x7,
        .addImm .x .x14 .x4 0, .addImm .x .x4 .x5 0, .addImm .x .x5 .x14 0] s = some s' ∧
      s'.gpr .x3 = s.gpr .x3 ^^^ s.gpr .x14 ∧
      s'.gpr .x4 = s.gpr .x5 ^^^ s.gpr .x14 ∧
      s'.gpr .x5 = s.gpr .x4 ^^^ ((s.gpr .x7 + s.gpr .x14) &&& 65535) ∧
      s'.gpr .x6 = s.gpr .x6 ^^^ ((s.gpr .x7 + s.gpr .x14) &&& 65535) ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x14] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, Nat.reduceLT, hm,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, Option.some.injEq, exists_eq_left', true_and]
  keep_tac

/-- The written registers of a round. -/
abbrev roundWrites : List Reg := [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14]

theorem Keep.weaken {rs : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : (rs.all fun r => roundWrites.contains r) = true) : Keep roundWrites s s' :=
  h.mono fun r hr => by
    have := List.all_eq_true.mp hs r hr
    simpa using this

theorem round_run (j : Nat) (hj : j < 8) (z : Spec.Idea.Schedule) (x : Spec.Idea.State)
    (s : State) (hx : Holds x s) (hk : KeyOk z s) (hm : MaskOk s) :
    ∃ s', runBlock isa (round j) s = some s' ∧
      Holds (Spec.Idea.round (z.getD (6 * j) 0) (z.getD (6 * j + 1) 0) (z.getD (6 * j + 2) 0)
        (z.getD (6 * j + 3) 0) (z.getD (6 * j + 4) 0) (z.getD (6 * j + 5) 0) x) s' ∧
      Keep roundWrites s s' := by
  obtain ⟨s₁, h₁, k0, k1, k2, k3, k4, k5, e₁⟩ := loads_run s j hj z hk
  have m₁ : MaskOk s₁ := (e₁.reg .x15 (by decide)).trans hm
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mul_run (d := .x3) .x3 (b := .x8) (by decide) s₁ m₁
  have m₂ : MaskOk s₂ := (e₂.reg .x15 (by decide)).trans m₁
  obtain ⟨s₃, h₃, v₃, e₃⟩ := lsr_run .x14 .x9 16 (by decide) s₂
  have m₃ : MaskOk s₃ := (e₃.reg .x15 (by decide)).trans m₂
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mul_run (d := .x6) .x6 (b := .x14) (by decide) s₃ m₃
  have m₄ : MaskOk s₄ := (e₄.reg .x15 (by decide)).trans m₃
  obtain ⟨s₅, h₅, v₅, e₅⟩ := lsr_run .x14 .x8 16 (by decide) s₄
  have m₅ : MaskOk s₅ := (e₅.reg .x15 (by decide)).trans m₄
  obtain ⟨s₆, h₆, v₆, e₆⟩ := addKey_run .x4 .x14 (by decide) s₅ m₅
  have m₆ : MaskOk s₆ := (e₆.reg .x15 (by decide)).trans m₅
  obtain ⟨s₇, h₇, v₇, e₇⟩ := addKey_run .x5 .x9 (by decide) s₆ m₆
  have m₇ : MaskOk s₇ := (e₇.reg .x15 (by decide)).trans m₆
  obtain ⟨s₈, h₈, v₈, e₈⟩ := eor_run .x7 .x3 .x5 s₇
  have m₈ : MaskOk s₈ := (e₈.reg .x15 (by decide)).trans m₇
  obtain ⟨s₉, h₉, v₉, e₉⟩ := mul_run (d := .x7) .x7 (b := .x13) (by decide) s₈ m₈
  have m₉ : MaskOk s₉ := (e₉.reg .x15 (by decide)).trans m₈
  obtain ⟨s₁₀, h₁₀, a₁₀, b₁₀, e₁₀⟩ := mid_run s₉
  have m₁₀ : MaskOk s₁₀ := (e₁₀.reg .x15 (by decide)).trans m₉
  obtain ⟨s₁₁, h₁₁, v₁₁, e₁₁⟩ := mul_run (d := .x14) .x14 (b := .x10) (by decide) s₁₀ m₁₀
  have m₁₁ : MaskOk s₁₁ := (e₁₁.reg .x15 (by decide)).trans m₁₀
  obtain ⟨s₁₂, h₁₂, r3, r4, r5, r6, e₁₂⟩ := tail_run s₁₁ m₁₁
  refine ⟨s₁₂, ?_, ?_, ?_⟩
  · simp only [round]
    exact run_append (run_append (run_append (run_append (run_append (run_append (run_append
      (run_append (run_append (run_append (run_append h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉) h₁₀) h₁₁)
      h₁₂
  · have x8₄ : s₄.gpr .x8 = s₁.gpr .x8 := by
      rw [e₄.reg .x8 (by decide), e₃.reg .x8 (by decide), e₂.reg .x8 (by decide)]
    have x9₆ : s₆.gpr .x9 = s₁.gpr .x9 := by
      rw [e₆.reg .x9 (by decide), e₅.reg .x9 (by decide), e₄.reg .x9 (by decide),
        e₃.reg .x9 (by decide), e₂.reg .x9 (by decide)]
    have a : s₇.gpr .x3 = (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0)).setWidth 64 := by
      rw [e₇.reg .x3 (by decide), e₆.reg .x3 (by decide), e₅.reg .x3 (by decide),
        e₄.reg .x3 (by decide), e₃.reg .x3 (by decide), v₂, e₁.reg .x3 (by decide), hx.x3,
        setWidth_setWidth16, k0]
    have d : s₇.gpr .x6 = (Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)).setWidth 64 := by
      rw [e₇.reg .x6 (by decide), e₆.reg .x6 (by decide), e₅.reg .x6 (by decide), v₄, v₃,
        e₃.reg .x6 (by decide), e₂.reg .x6 (by decide), e₁.reg .x6 (by decide), hx.x6,
        setWidth_setWidth16, e₂.reg .x9 (by decide), k3]
    have b : s₇.gpr .x4 = (x.getD 1 0 + z.getD (6 * j + 1) 0).setWidth 64 := by
      rw [e₇.reg .x4 (by decide), v₆, v₅, e₅.reg .x4 (by decide), e₄.reg .x4 (by decide),
        e₃.reg .x4 (by decide), e₂.reg .x4 (by decide), e₁.reg .x4 (by decide), hx.x4, x8₄,
        add_mask, k1]
    have c : s₇.gpr .x5 = (x.getD 2 0 + z.getD (6 * j + 2) 0).setWidth 64 := by
      rw [v₇, x9₆, e₆.reg .x5 (by decide), e₅.reg .x5 (by decide), e₄.reg .x5 (by decide),
        e₃.reg .x5 (by decide), e₂.reg .x5 (by decide), e₁.reg .x5 (by decide), hx.x5, add_mask, k2]
    have x13₉ : s₈.gpr .x13 = s₁.gpr .x13 := by
      rw [e₈.reg .x13 (by decide), e₇.reg .x13 (by decide), e₆.reg .x13 (by decide),
        e₅.reg .x13 (by decide), e₄.reg .x13 (by decide), e₃.reg .x13 (by decide),
        e₂.reg .x13 (by decide)]
    have t₀ : s₉.gpr .x7 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
        (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0)).setWidth 64 := by
      rw [v₉, v₈, a, c, xor_setWidth, setWidth_setWidth16, x13₉, k4]
    have keep₉ : ∀ r ∈ [Reg.x3, .x4, .x5, .x6], s₉.gpr r = s₇.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact (e₉.reg _ (by decide)).trans (e₈.reg _ (by decide))
    have t₁ : s₁₁.gpr .x14 = (Spec.Idea.mul (((x.getD 1 0 + z.getD (6 * j + 1) 0) ^^^
        Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
          (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0))
        (z.getD (6 * j + 5) 0)).setWidth 64 := by
      rw [v₁₁, a₁₀, b₁₀, keep₉ .x4 (by simp), keep₉ .x6 (by simp), b, d, t₀, xor_setWidth,
        add_setWidth, e₉.reg .x13 (by decide), x13₉, k5]
    have keep₁₁ : ∀ r ∈ [Reg.x3, .x4, .x5, .x6], s₁₁.gpr r = s₇.gpr r := by
      intro r hr
      have h := keep₉ r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact (e₁₁.reg _ (by decide)).trans ((e₁₀.reg _ (by decide)).trans h)
    have x7₁₁ : s₁₁.gpr .x7 = s₉.gpr .x7 := by
      rw [e₁₁.reg .x7 (by decide), e₁₀.reg .x7 (by decide)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [r3, keep₁₁ .x3 (by simp), a, t₁, xor_setWidth]; rfl
    · rw [r4, keep₁₁ .x5 (by simp), c, t₁, xor_setWidth]; rfl
    · rw [r5, keep₁₁ .x4 (by simp), b, x7₁₁, t₀, t₁, add_mask, setWidth_setWidth16, xor_setWidth]; rfl
    · rw [r6, keep₁₁ .x6 (by simp), d, x7₁₁, t₀, t₁, add_mask, setWidth_setWidth16, xor_setWidth]; rfl
  · exact ((((((((((((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))).trans (e₄.weaken (by decide))).trans (e₅.weaken (by decide))).trans (e₆.weaken (by decide))).trans (e₇.weaken (by decide))).trans (e₈.weaken (by decide))).trans (e₉.weaken (by decide))).trans (e₁₀.weaken (by decide))).trans (e₁₁.weaken (by decide))).trans (e₁₂.weaken (by decide)))

end VG.Proof.Idea.AArch64
