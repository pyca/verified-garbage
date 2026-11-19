module

public import VerifiedGarbage.Proof.Idea.AArch64.Mul
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Spec.Idea.Contract
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Idea.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Idea.Arith
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.CallLay

/-! ### `Idea.AArch64.Block`, which this module and modules that import it used -/

section

/-! ### `Idea.AArch64.Round`, which this module and modules that import it used -/

section

/-!
# IDEA on AArch64: a round

`round_run`: round `j` of the code maps the state words in `x3`–`x6`
(`Holds`) to `Spec.Idea.round` of them under subkeys `6j … 6j + 5`, loaded
two at a time from the schedule at `x0` (`KeyOk`).
-/

@[expose] public section

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
  read : InRegions (s.rd ++ s.wr) (s.gpr .x0) 104
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
  refine ⟨CallLay.inRegions_sub h.read (by omega_using [hk]) (by decide), ?_, ?_⟩
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
  ⟨CallLay.inRegions_sub h.read (by decide) (by decide), fun j hj => by
    rw [subkey_read96 _ _ hj, h.sched]⟩

tactic_template "keep_tac" : tactic => `(tactic| (
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
  obtain p₀ := hk.pair (k := 3 * j) (by omega_using [hj])
  obtain p₁ := hk.pair (k := 3 * j + 1) (by omega_using [hj])
  obtain p₂ := hk.pair (k := 3 * j + 2) (by omega_using [hj])
  rw [show 4 * (3 * j) = 12 * j by omega_using [], show 2 * (3 * j) + 1 = 6 * j + 1 by omega_using [],
    show 2 * (3 * j) = 6 * j by omega_using []] at p₀
  rw [show 4 * (3 * j + 1) = 12 * j + 4 by omega_using [], show 2 * (3 * j + 1) + 1 = 6 * j + 3 by omega_using [],
    show 2 * (3 * j + 1) = 6 * j + 2 by omega_using []] at p₁
  rw [show 4 * (3 * j + 2) = 12 * j + 8 by omega_using [], show 2 * (3 * j + 2) + 1 = 6 * j + 5 by omega_using [],
    show 2 * (3 * j + 2) = 6 * j + 4 by omega_using []] at p₂
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, isa, Size.bytes,
    show (12 * j) % 4 = 0 by omega_using [], show 12 * j < 4096 * 4 by omega_using [hj],
    show (12 * j + 4) % 4 = 0 by omega_using [], show 12 * j + 4 < 4096 * 4 by omega_using [hj],
    show (12 * j + 8) % 4 = 0 by omega_using [], show 12 * j + 8 < 4096 * 4 by omega_using [hj], and_self, ↓reduceIte,
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
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
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
  obtain m₁ : MaskOk s₁ := (e₁.reg .x15 (by decide)).trans hm
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mul_run (d := .x3) .x3 (b := .x8) (by decide) s₁ m₁
  obtain m₂ : MaskOk s₂ := (e₂.reg .x15 (by decide)).trans m₁
  obtain ⟨s₃, h₃, v₃, e₃⟩ := lsr_run .x14 .x9 16 (by decide) s₂
  obtain m₃ : MaskOk s₃ := (e₃.reg .x15 (by decide)).trans m₂
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mul_run (d := .x6) .x6 (b := .x14) (by decide) s₃ m₃
  obtain m₄ : MaskOk s₄ := (e₄.reg .x15 (by decide)).trans m₃
  obtain ⟨s₅, h₅, v₅, e₅⟩ := lsr_run .x14 .x8 16 (by decide) s₄
  obtain m₅ : MaskOk s₅ := (e₅.reg .x15 (by decide)).trans m₄
  obtain ⟨s₆, h₆, v₆, e₆⟩ := addKey_run .x4 .x14 (by decide) s₅ m₅
  obtain m₆ : MaskOk s₆ := (e₆.reg .x15 (by decide)).trans m₅
  obtain ⟨s₇, h₇, v₇, e₇⟩ := addKey_run .x5 .x9 (by decide) s₆ m₆
  obtain m₇ : MaskOk s₇ := (e₇.reg .x15 (by decide)).trans m₆
  obtain ⟨s₈, h₈, v₈, e₈⟩ := eor_run .x7 .x3 .x5 s₇
  obtain m₈ : MaskOk s₈ := (e₈.reg .x15 (by decide)).trans m₇
  obtain ⟨s₉, h₉, v₉, e₉⟩ := mul_run (d := .x7) .x7 (b := .x13) (by decide) s₈ m₈
  obtain m₉ : MaskOk s₉ := (e₉.reg .x15 (by decide)).trans m₈
  obtain ⟨s₁₀, h₁₀, a₁₀, b₁₀, e₁₀⟩ := mid_run s₉
  obtain m₁₀ : MaskOk s₁₀ := (e₁₀.reg .x15 (by decide)).trans m₉
  obtain ⟨s₁₁, h₁₁, v₁₁, e₁₁⟩ := mul_run (d := .x14) .x14 (b := .x10) (by decide) s₁₀ m₁₀
  obtain m₁₁ : MaskOk s₁₁ := (e₁₁.reg .x15 (by decide)).trans m₁₀
  obtain ⟨s₁₂, h₁₂, r3, r4, r5, r6, e₁₂⟩ := tail_run s₁₁ m₁₁
  refine ⟨s₁₂, ?_, ?_, ?_⟩
  · simp only [round]
    exact run_append (run_append (run_append (run_append (run_append (run_append (run_append
      (run_append (run_append (run_append (run_append h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉) h₁₀) h₁₁)
      h₁₂
  · have x8₄ : s₄.gpr .x8 = s₁.gpr .x8 := by
      rw [e₄.reg .x8 (by decide), e₃.reg .x8 (by decide), e₂.reg .x8 (by decide)]
    obtain x9₆ : s₆.gpr .x9 = s₁.gpr .x9 := by
      rw [e₆.reg .x9 (by decide), e₅.reg .x9 (by decide), e₄.reg .x9 (by decide),
        e₃.reg .x9 (by decide), e₂.reg .x9 (by decide)]
    obtain a : s₇.gpr .x3 = (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0)).setWidth 64 := by
      rw [e₇.reg .x3 (by decide), e₆.reg .x3 (by decide), e₅.reg .x3 (by decide),
        e₄.reg .x3 (by decide), e₃.reg .x3 (by decide), v₂, e₁.reg .x3 (by decide), hx.x3,
        setWidth_setWidth16, k0]
    obtain d : s₇.gpr .x6 = (Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)).setWidth 64 := by
      rw [e₇.reg .x6 (by decide), e₆.reg .x6 (by decide), e₅.reg .x6 (by decide), v₄, v₃,
        e₃.reg .x6 (by decide), e₂.reg .x6 (by decide), e₁.reg .x6 (by decide), hx.x6,
        setWidth_setWidth16, e₂.reg .x9 (by decide), k3]
    obtain b : s₇.gpr .x4 = (x.getD 1 0 + z.getD (6 * j + 1) 0).setWidth 64 := by
      rw [e₇.reg .x4 (by decide), v₆, v₅, e₅.reg .x4 (by decide), e₄.reg .x4 (by decide),
        e₃.reg .x4 (by decide), e₂.reg .x4 (by decide), e₁.reg .x4 (by decide), hx.x4, x8₄,
        add_mask, k1]
    obtain c : s₇.gpr .x5 = (x.getD 2 0 + z.getD (6 * j + 2) 0).setWidth 64 := by
      rw [v₇, x9₆, e₆.reg .x5 (by decide), e₅.reg .x5 (by decide), e₄.reg .x5 (by decide),
        e₃.reg .x5 (by decide), e₂.reg .x5 (by decide), e₁.reg .x5 (by decide), hx.x5, add_mask, k2]
    obtain x13₉ : s₈.gpr .x13 = s₁.gpr .x13 := by
      rw [e₈.reg .x13 (by decide), e₇.reg .x13 (by decide), e₆.reg .x13 (by decide),
        e₅.reg .x13 (by decide), e₄.reg .x13 (by decide), e₃.reg .x13 (by decide),
        e₂.reg .x13 (by decide)]
    obtain t₀ : s₉.gpr .x7 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
        (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0)).setWidth 64 := by
      rw [v₉, v₈, a, c, xor_setWidth, setWidth_setWidth16, x13₉, k4]
    obtain keep₉ : ∀ r ∈ [Reg.x3, .x4, .x5, .x6], s₉.gpr r = s₇.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact (e₉.reg _ (by decide)).trans (e₈.reg _ (by decide))
    obtain t₁ : s₁₁.gpr .x14 = (Spec.Idea.mul (((x.getD 1 0 + z.getD (6 * j + 1) 0) ^^^
        Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
          (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0))
        (z.getD (6 * j + 5) 0)).setWidth 64 := by
      rw [v₁₁, a₁₀, b₁₀, keep₉ .x4 (by simp), keep₉ .x6 (by simp), b, d, t₀, xor_setWidth,
        add_setWidth, e₉.reg .x13 (by decide), x13₉, k5]
    obtain keep₁₁ : ∀ r ∈ [Reg.x3, .x4, .x5, .x6], s₁₁.gpr r = s₇.gpr r := by
      intro r hr
      obtain h := keep₉ r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact (e₁₁.reg _ (by decide)).trans ((e₁₀.reg _ (by decide)).trans h)
    obtain x7₁₁ : s₁₁.gpr .x7 = s₉.gpr .x7 := by
      rw [e₁₁.reg .x7 (by decide), e₁₀.reg .x7 (by decide)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [r3, keep₁₁ .x3 (by simp), a, t₁, xor_setWidth]; rfl
    · rw [r4, keep₁₁ .x5 (by simp), c, t₁, xor_setWidth]; rfl
    · rw [r5, keep₁₁ .x4 (by simp), b, x7₁₁, t₀, t₁, add_mask, setWidth_setWidth16, xor_setWidth]; rfl
    · rw [r6, keep₁₁ .x6 (by simp), d, x7₁₁, t₀, t₁, add_mask, setWidth_setWidth16, xor_setWidth]; rfl
  · exact ((((((((((((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))).trans (e₄.weaken (by decide))).trans (e₅.weaken (by decide))).trans (e₆.weaken (by decide))).trans (e₇.weaken (by decide))).trans (e₈.weaken (by decide))).trans (e₉.weaken (by decide))).trans (e₁₀.weaken (by decide))).trans (e₁₁.weaken (by decide))).trans (e₁₂.weaken (by decide)))

end VG.Proof.Idea.AArch64

end

end

/-!
# IDEA on AArch64: a block

`cryptBlock_run`: `Impl.Idea.AArch64.cryptBlock` replaces the block at `x1`
with `Spec.Idea.cryptBlock` of it under the subkeys at `x0`.
-/

@[expose] public section

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
  obtain h0 := hb (2 * k) (by omega_using [hk])
  obtain h1 := hb (2 * k + 1) (by omega_using [hk])
  simp only [loadWord, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, isa,
    State.read, Size.bits, Nat.mod_one, show 2 * k < 4096 * 1 by omega_using [hk],
    show 2 * k + 1 < 4096 * 1 by omega_using [hk], and_self, ↓reduceIte, Option.bind_some, Option.map_some,
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
    obtain ⟨s₁, h₁, x₁, e₁⟩ := rounds_run z x n (by omega_using [hn]) s hx hk hm
    obtain ⟨s₂, h₂, x₂, e₂⟩ := round_run n (by omega_using [hn]) z _ s₁ x₁ (hk.keep e₁ (by decide))
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
  obtain m₁ : MaskOk s₁ := (e₁.reg .x15 (by decide)).trans hm
  obtain l0 := hv 0 (by decide)
  obtain l1 := hv 1 (by decide)
  obtain l2 := hv 2 (by decide)
  obtain l3 := hv 3 (by decide)
  simp only [Nat.mul_zero, BitVec.ushiftRight_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at l0 l1 l2 l3
  rw [← v₁] at l0 l1 l2 l3
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mul_run (d := .x3) .x3 (b := .x8) (by decide) s₁ m₁
  obtain m₂ : MaskOk s₂ := (e₂.reg .x15 (by decide)).trans m₁
  obtain ⟨s₃, h₃, v₃, e₃⟩ := lsr_run .x14 .x8 48 (by decide) s₂
  obtain m₃ : MaskOk s₃ := (e₃.reg .x15 (by decide)).trans m₂
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mul_run (d := .x6) .x6 (b := .x14) (by decide) s₃ m₃
  obtain m₄ : MaskOk s₄ := (e₄.reg .x15 (by decide)).trans m₃
  obtain ⟨s₅, h₅, v₅, e₅⟩ := lsr_run .x14 .x8 16 (by decide) s₄
  obtain m₅ : MaskOk s₅ := (e₅.reg .x15 (by decide)).trans m₄
  obtain ⟨s₆, h₆, v₆, e₆⟩ := addKey_run .x5 .x14 (by decide) s₅ m₅
  obtain m₆ : MaskOk s₆ := (e₆.reg .x15 (by decide)).trans m₅
  obtain ⟨s₇, h₇, v₇, e₇⟩ := lsr_run .x14 .x8 32 (by decide) s₆
  obtain m₇ : MaskOk s₇ := (e₇.reg .x15 (by decide)).trans m₆
  obtain ⟨s₈, h₈, v₈, e₈⟩ := addKey_run .x4 .x14 (by decide) s₇ m₇
  obtain x8₇ : s₆.gpr .x8 = s₁.gpr .x8 := by
    rw [e₆.reg .x8 (by decide), e₅.reg .x8 (by decide),
      e₄.reg .x8 (by decide), e₃.reg .x8 (by decide), e₂.reg .x8 (by decide)]
  obtain x8₅ : s₄.gpr .x8 = s₁.gpr .x8 := by
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
    rw [storeWord, strb_cons (by omega_using [hk]) ha h1, runBlock_cons, exec_lsr_x (by decide), runStep_some,
      strb_cons (a := a) (by omega_using [hk]) ?_ ?_, runBlock_nil]
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
  h.write (List.mem_singleton_self _) (n := 1) v (Offset.contains_base a (by omega_using [hj]) (by omega_using [hj]))

theorem store_run (y : Spec.Idea.State) (s : State) {a : Addr} (ha : s.gpr .x1 = a)
    (hw : BlockWrite s a) (hy : OutHolds y s) :
    ∃ s', runBlock isa store s = some s' ∧
      Spec.Idea.blockAt s'.mem a = Spec.Idea.encodeBlock y ∧
      Frame [⟨a, 8⟩] s.mem s'.mem ∧ (∀ q, q ≠ .x14 → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, h₁, m₁, g₁, rd₁, wr₁, sp₁⟩ :=
    storeWord_run .x3 0 (by decide) s ha (hw _ (by decide)) (hw _ (by decide))
  obtain ha₁ : s₁.gpr .x1 = a := (g₁ .x1 (by decide)).trans ha
  obtain hw₁ : BlockWrite s₁ a := fun i hi => wr₁ ▸ hw i hi
  obtain ⟨s₂, h₂, m₂, g₂, rd₂, wr₂, sp₂⟩ :=
    storeWord_run .x5 1 (by decide) s₁ ha₁ (hw₁ _ (by decide)) (hw₁ _ (by decide))
  obtain ha₂ : s₂.gpr .x1 = a := (g₂ .x1 (by decide)).trans ha₁
  obtain hw₂ : BlockWrite s₂ a := fun i hi => wr₂ ▸ hw₁ i hi
  obtain ⟨s₃, h₃, m₃, g₃, rd₃, wr₃, sp₃⟩ :=
    storeWord_run .x4 2 (by decide) s₂ ha₂ (hw₂ _ (by decide)) (hw₂ _ (by decide))
  obtain ha₃ : s₃.gpr .x1 = a := (g₃ .x1 (by decide)).trans ha₂
  obtain hw₃ : BlockWrite s₃ a := fun i hi => wr₃ ▸ hw₂ i hi
  obtain ⟨s₄, h₄, m₄, g₄, rd₄, wr₄, sp₄⟩ :=
    storeWord_run .x6 3 (by decide) s₃ ha₃ (hw₃ _ (by decide)) (hw₃ _ (by decide))
  obtain v5 : s₁.gpr .x5 = (y.getD 1 0).setWidth 64 := (g₁ .x5 (by decide)).trans hy.x5
  obtain v4 : s₂.gpr .x4 = (y.getD 2 0).setWidth 64 :=
    (g₂ .x4 (by decide)).trans ((g₁ .x4 (by decide)).trans hy.x4)
  obtain v6 : s₃.gpr .x6 = (y.getD 3 0).setWidth 64 :=
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
        i = 5 ∨ i = 6 ∨ i = 7 := by omega_using [hi]
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
  obtain k₁ := hk.keep e₁ (by decide)
  obtain m₁ : MaskOk s₁ := (e₁.reg .x15 (by decide)).trans hm
  obtain ⟨s₂, h₂, x₂, e₂⟩ := rounds_run z _ 8 (by decide) s₁ x₁ k₁ m₁
  obtain ⟨s₃, h₃, x₃, e₃⟩ := output_run z _ s₂ x₂ (k₁.keep e₂ (by decide))
    ((e₂.reg .x15 (by decide)).trans m₁)
  obtain e₁₃ := ((e₁.weaken (by decide)).trans e₂).trans e₃
  obtain ⟨s₄, h₄, b₄, f₄, g₄, rd₄, wr₄, sp₄⟩ := store_run _ s₃ ((e₁₃.reg .x1 (by decide)).trans ha)
    (fun i hi => e₁₃.wr ▸ hw i hi) x₃
  refine ⟨s₄, ?_, ?_, ?_, fun q hq => ?_, rd₄.trans e₁₃.rd, wr₄.trans e₁₃.wr, sp₄.trans e₁₃.sp⟩
  · simp only [cryptBlock]
    exact run_append (run_append (run_append h₁ h₂) h₃) h₄
  · rw [b₄, Spec.Idea.cryptBlock, crypt_eq]
  · rw [← e₁₃.mem]; exact f₄
  · rw [g₄ q (by intro h; subst h; exact hq (by decide)), e₁₃.reg q hq]

end VG.Proof.Idea.AArch64

end

end

/-!
# IDEA ECB on AArch64

`ecb_verified`: `Impl.Idea.AArch64.ecb` meets the shared ECB contract, with
no stack. The blocks are transformed in a loop (`loop_ok`) whose invariant
(`LoopInv`) says how many remain, that the ones before are transformed and
the ones after not yet; each iteration is `cryptBlock_run`.
-/

@[expose] public section

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.Impl.Idea.AArch64

/-! ## The loop -/

theorem advance_run (s : State) :
    ∃ s', runBlock isa [.addImm .x .x1 .x1 8, .subImm .x .x2 .x2 1] s = some s' ∧
      s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 8 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      Keep [.x1, .x2] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
    Nat.reduceLT, ↓reduceIte, BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq, ofNat_one,
    Option.some.injEq, exists_eq_left', true_and]
  keep_tac

/-- The registers the loop writes. -/
abbrev loopWrites : List Reg := [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12,
  .x13, .x14]

/-- The facts about the state `o` before the loop that the loop relies on:
the schedule `z` at `x0`, readable, and `n` blocks at `a`, writable, apart
from it and not wrapping around, and the mask in `x15`. -/
structure LoopCtx (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (o : State) : Prop where
  sched : ⟨o.gpr .x0, 104⟩ ∈ o.rd ++ o.wr
  data : ⟨a, 8 * n⟩ ∈ o.wr
  z : Spec.Idea.scheduleAt o.mem (o.gpr .x0) = z
  sep : (⟨o.gpr .x0, 104⟩ : Region).Disjoint ⟨a, 8 * n⟩
  bound : 8 * n ≤ 2 ^ 64
  mask : MaskOk o

/-- `r` blocks remain, at `a + 8 (n - r)` on: the ones before are transformed. -/
structure LoopInv (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (m₀ : Mem) (o : State) (r : Nat)
    (t : State) : Prop where
  pos : 1 ≤ r
  le : r ≤ n
  x1 : t.gpr .x1 = a + BitVec.ofNat 64 (8 * (n - r))
  x2 : t.gpr .x2 = BitVec.ofNat 64 r
  keep : Keep loopWrites o { t with mem := o.mem }
  frame : Frame [⟨a, 8 * n⟩] o.mem t.mem
  done : ∀ j < n - r, Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j)))
  todo : ∀ j, n - r ≤ j → j < n → Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))

/-- After the loop: every block transformed. -/
structure LoopPost (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (m₀ : Mem) (o : State)
    (t : State) : Prop where
  keep : Keep loopWrites o { t with mem := o.mem }
  frame : Frame [⟨a, 8 * n⟩] o.mem t.mem
  done : ∀ j < n, Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j)))

theorem step_ok {z : Spec.Idea.Schedule} {a : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z a n o) (r : Nat) (t : State) (hi : LoopInv z a n m₀ o r t) :
    WP isa (.block (cryptBlock ++ ([.addImm .x .x1 .x1 8, .subImm .x .x2 .x2 1] : List Instr))) t
      (fun t' => (isa.eval (.nonzero .x .x2) t' = some false ∧ LoopPost z a n m₀ o t') ∨
        (isa.eval (.nonzero .x .x2) t' = some true ∧ ∃ r' < r, LoopInv z a n m₀ o r' t')) := by
  have hrd : t.rd = o.rd := hi.keep.rd
  have hwr : t.wr = o.wr := hi.keep.wr
  have hx0 : t.gpr .x0 = o.gpr .x0 := hi.keep.reg .x0 (by decide)
  have hj : n - r < n := by have := hi.pos; have := hi.le; omega_arith
  -- The block and the schedule.
  have hread : BlockRead t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hrd, hwr]; exact List.mem_append_right _ hc.data,
      block_contains hj (by omega_using [hi']) (by decide) hc.bound⟩
  have hwrite : BlockWrite t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hwr]; exact hc.data, block_contains hj (by omega_using [hi']) (by decide) hc.bound⟩
  have hk : KeyOk z t := by
    refine ⟨by rw [hx0, hrd, hwr]; exact ⟨_, hc.sched, Region.contains_self _ _⟩, ?_⟩
    rw [hx0, ← hc.z]
    exact scheduleAt_congr (frame_bytes hi.frame (by simpa using hc.sep) (by decide))
  have hm : MaskOk t := (hi.keep.reg .x15 (by decide)).trans hc.mask
  obtain ⟨t₁, h₁, b₁, f₁, g₁, rd₁, wr₁, sp₁⟩ := cryptBlock_run z t hi.x1 hread hwrite hk hm
  obtain ⟨t₂, h₂, x1₂, x2₂, e₂⟩ := advance_run t₁
  refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_⟩
  -- What holds after the iteration, whether it is the last or not.
  have keep₂ : Keep loopWrites o { t₂ with mem := o.mem } := by
    refine ⟨fun q hq => ?_, rfl, ?_, ?_, ?_⟩
    · show t₂.gpr q = o.gpr q
      have s₁ : ∀ q, q ∈ [Reg.x1, .x2] → q ∈ loopWrites := by decide
      have s₂ : ∀ q, q ∈ roundWrites → q ∈ loopWrites := by decide
      rw [e₂.reg q (fun h => hq (s₁ q h)), g₁ q (fun h => hq (s₂ q h))]
      exact hi.keep.reg q hq
    · show t₂.rd = o.rd; rw [e₂.rd, rd₁, hrd]
    · show t₂.wr = o.wr; rw [e₂.wr, wr₁, hwr]
    · show t₂.sp = o.sp; rw [e₂.sp, sp₁]; exact hi.keep.sp
  have mem₂ : t₂.mem = t₁.mem := e₂.mem
  have frame₂ : Frame [⟨a, 8 * n⟩] o.mem t₂.mem := by
    rw [mem₂]
    refine hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base a (by omega_using [hj])
  have other (j : Nat) (hjn : j < n) (hne : j ≠ n - r) :
      Spec.Idea.blockAt t₂.mem (a + BitVec.ofNat 64 (8 * j)) =
        Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) := by
    rw [mem₂]
    exact blockAt_congr (frame_bytes f₁ (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact blocks_disjoint hj hjn (Ne.symm hne) hc.bound) (by decide))
  have done₂ : ∀ j < n - (r - 1), Spec.Idea.blockAt t₂.mem (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))) := by
    intro j hjr
    by_cases he : j = n - r
    · subst he
      rw [mem₂, b₁, hi.todo _ (Nat.le_refl _) hj]
    · rw [other j (by omega_using [hjr]) he]
      exact hi.done j (by have := hi.pos; omega_using [hjr, he])
  have hx2 : t₂.gpr .x2 = BitVec.ofNat 64 (r - 1) := by
    rw [x2₂, g₁ .x2 (by decide), hi.x2]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le; have := hc.bound
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, toNat_one]
    omega_using [hj]
  have hev : isa.eval (.nonzero .x .x2) t₂ = some (decide (r - 1 ≠ 0)) := by
    have := hi.le; have := hc.bound
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2, bne,
      beq_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r - 1 < 2 ^ 64 by omega_arith), decide_not]
  by_cases hlast : r = 1
  · subst hlast
    left
    exact ⟨hev, keep₂, frame₂, fun j hjn => done₂ j (by omega_using [hjn])⟩
  · right
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega_using [hj, hlast],
      r - 1, by have := hi.pos; omega_using [hj], ?_⟩
    refine ⟨by have := hi.pos; omega_using [hj, hlast], by have := hi.le; omega_using [this], ?_, hx2, keep₂, frame₂, done₂, ?_⟩
    · rw [x1₂, g₁ .x1 (by decide), hi.x1, Offset.add_ofNat_add_ofNat]
      congr 2
      have := hi.pos; have := hi.le
      omega_using [hj, this]
    · intro j hj₁ hj₂
      have := hi.pos
      have := hi.le
      have hne : j ≠ n - r := by omega_using [hj, hj₁, this]
      rw [other j hj₂ hne]
      exact hi.todo j (by omega_using [hj₁]) hj₂

theorem loop_ok {z : Spec.Idea.Schedule} {a : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z a n o) (hn : 1 ≤ n) (ho : o.gpr .x1 = a) (hx2 : o.gpr .x2 = BitVec.ofNat 64 n)
    (htodo : ∀ j < n, Spec.Idea.blockAt o.mem (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))) :
    WP isa (.loop (.block (cryptBlock ++ ([.addImm .x .x1 .x1 8, .subImm .x .x2 .x2 1] : List Instr)))
      (.nonzero .x .x2)) o (LoopPost z a n m₀ o) := by
  refine WP.loop (M := isa) (LoopInv z a n m₀ o) (fun r t hi => step_ok hc r t hi) n o
    ⟨hn, Nat.le_refl _, ?_, hx2, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, Frame.refl _ _,
      fun j hj => by omega, fun j _ hj => htodo j hj⟩
  rw [Nat.sub_self, Nat.mul_zero, ho]; exact (BitVec.add_zero a).symm

/-! ## The function -/

/-- The ECB contract on AArch64. -/
def contract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 104⟩
    let data : Region := ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
    s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧
      (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' := Spec.Idea.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
    Spec.Idea.ecb (Spec.Idea.scheduleAt s.mem (s.gpr .x0))
      (Spec.Idea.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub := PublicRegs [.x0, .x1, .x2]

theorem setMask_run (s : State) :
    ∃ s', runBlock isa [setMask] s = some s' ∧ MaskOk s' ∧ Keep [.x15] s s' := by
  simp only [setMask, runBlock_cons, runStep_some, runBlock_nil, exec, isa, Size.bits,
    Nat.mul_zero, Nat.reduceLT, ↓reduceIte, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, by keep_tac⟩

theorem ecb_wp (s : State) (hs : contract.pre s) :
    WP isa ecb s (fun s' => GprAbi s s' ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, dSched, hbound⟩ := hs
  have hz : isa.eval (.zero .x .x2) s = some (decide ((s.gpr .x2).toNat = 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, beq_zero]
  apply WP.ite _ hz
  · -- No blocks.
    intro h0
    have hn : (s.gpr .x2).toNat = 0 := by simpa using h0
    refine WP.block_nil ⟨⟨fun r _ => rfl, rfl⟩, ?_⟩
    show Spec.Idea.blocksAt s.mem _ _ = _
    rw [hn]; rfl
  · intro h0
    have hn : (s.gpr .x2).toNat ≠ 0 := by simpa using h0
    apply WP.seq
    apply WP.of_runBlock
    obtain ⟨s₁, h₁, m₁, e₁⟩ := setMask_run s
    refine ⟨s₁, h₁, ?_⟩
    have ctx : LoopCtx (Spec.Idea.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x1) (s.gpr .x2).toNat s₁ := by
      refine ⟨?_, ?_, ?_, ?_, by omega_using [hbound], m₁⟩
      · rw [e₁.reg .x0 (by decide), e₁.rd, e₁.wr, hrd]; simp
      · rw [e₁.wr, hwr]; simp
      · rw [e₁.reg .x0 (by decide), e₁.mem]
      · rw [e₁.reg .x0 (by decide)]; exact dSched
    refine WP.mono (loop_ok ctx (Nat.pos_of_ne_zero hn) (e₁.reg .x1 (by decide))
      (by rw [e₁.reg .x2 (by decide), ofNat_toNat64]) (m₀ := s.mem)
      (fun j _ => by rw [e₁.mem])) fun t ht => ?_
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · have hr' : r ∉ loopWrites := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hr₁ : r ∉ [Reg.x15] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (ht.keep.reg r hr').trans (e₁.reg r hr₁)
    · exact ht.keep.sp.trans e₁.sp
    · show Spec.Idea.blocksAt t.mem (s.gpr .x1) (s.gpr .x2).toNat = _
      exact blocksAt_eq _ _ _ _ _ ht.done

theorem ecb_correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa ecb s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_wp s hs
  exact ⟨t, s', he, ⟨ha.1, ha.2, Exec.preservedV he (by lit_decide)⟩, hp⟩

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 1 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩]

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 := by
  simp [PublicRegs]

theorem ecb_verified : Verified target ecb (Spec.Idea.ecbContract abi 0) := by
  refine Verified.of_correct ecb_correct (ecb_constantTime _) ?_
  sig_implies [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Spec.Idea.ecbPost, abi, argRegs, contract,
    publicRegs_three] [satState] using satState

end VG.Proof.Idea.AArch64
