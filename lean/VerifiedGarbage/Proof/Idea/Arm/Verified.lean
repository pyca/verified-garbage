module

public import VerifiedGarbage.Proof.Idea.Arm.Mul
import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Idea.Scratch32
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Idea.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Idea.Inverse
import VerifiedGarbage.Proof.Idea.KeyBits32
import VerifiedGarbage.Proof.Idea.Arith32
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Framework.Arm.RegScratch
import VerifiedGarbage.Proof.Idea.Local
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Idea.Memory32

/-! ### `Idea.Arm.Block`, which only this module used -/

section

/-! ### `Idea.Arm.Round`, which this module and modules that import it used -/

section

/-!
# IDEA on ARMv7: a round

`round_run`: round `j` of the code (`roundWith j b c`) maps the state words
in `r4`, `b`, `c`, `r7` (`Holds`) to `Spec.Idea.round` of them under subkeys
`6j … 6j + 5`, each loaded from the schedule at `r0` (`KeyOk`) when it is
used, and leaves the new middle words in `c` and `b`.
-/

@[expose] public section

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Impl.Idea.Arm

/-- The state words are in `r4`, `b`, `c`, `r7`, zero-extended. -/
structure Holds (x : Spec.Idea.State) (b c : Reg) (s : State) : Prop where
  r4 : s.gpr .r4 = (x.getD 0 0).setWidth 32
  b : s.gpr b = (x.getD 1 0).setWidth 32
  c : s.gpr c = (x.getD 2 0).setWidth 32
  r7 : s.gpr .r7 = (x.getD 3 0).setWidth 32

/-- The schedule `z` is at `r0`, readable, and does not wrap around. -/
structure KeyOk (z : Spec.Idea.Schedule) (s : State) : Prop where
  read : ⟨State.addr (s.gpr .r0), 104⟩ ∈ s.rd ++ s.wr
  fit : (s.gpr .r0).toNat + 104 ≤ 2 ^ 32
  sched : Spec.Idea.scheduleAt s.mem (State.addr (s.gpr .r0)) = z

theorem KeyOk.keep {z : Spec.Idea.Schedule} {rs : List Reg} {s s' : State} (h : KeyOk z s)
    (hk : Keep rs s s') (hr0 : .r0 ∉ rs) : KeyOk z s' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hk.rd, hk.wr, hk.reg .r0 hr0]; exact h.read
  · rw [hk.reg .r0 hr0]; exact h.fit
  · rw [hk.mem, hk.reg .r0 hr0]; exact h.sched

theorem ldr_key_run (r : Reg) (off : Nat) (hoff : off ≤ 100) {z : Spec.Idea.Schedule} (s : State)
    (hk : KeyOk z s) :
    ∃ s', runBlock isa [.ldr r .r0 off] s = some s' ∧
      s'.gpr r = s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 off) 32 ∧ Keep [r] s s' := by
  obtain hfit : (s.gpr .r0).toNat + off < 2 ^ 32 := by have := hk.fit; omega_using [hoff, this]
  obtain hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 off)) 4 := by
    rw [addr_add hfit]
    exact ⟨_, hk.read, Offset.contains_base _ (by omega_using [hoff]) (by omega_using [hoff])⟩
  refine ⟨_, by rw [runBlock_cons, exec_ldr (by omega_using [hoff]) hin, runStep_some, runBlock_nil], ?_, ?_⟩
  · rw [RegUpd.gpr_setReg_self, addr_add hfit]
  · keep_tac

/-- `loadKey r k`: subkey `k` in the low 16 bits of `r`. -/
theorem loadKey_run (r : Reg) (k : Nat) (hk52 : k < 52) {z : Spec.Idea.Schedule} (s : State)
    (hk : KeyOk z s) :
    ∃ s', runBlock isa (loadKey r k) s = some s' ∧ (s'.gpr r).setWidth 16 = z.getD k 0 ∧
      Keep [r] s s' := by
  unfold loadKey
  split
  · rename_i h; subst h
    obtain ⟨s₁, h₁, v₁, e₁⟩ := ldr_key_run r 100 (by decide) s hk
    refine ⟨s₁.setReg r (s₁.gpr r >>> 16), ?_, ?_, ?_⟩
    · rw [show ([.ldr r .r0 100, .mov r (.shifted r .lsr 16)] : List Instr) =
        [.ldr r .r0 100] ++ [.mov r (.shifted r .lsr 16)] from rfl]
      refine run_append h₁ ?_
      simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval,
        Nat.reduceLeDiff, and_self, ↓reduceIte, Option.map_some]
    · rw [RegUpd.gpr_setReg_self, v₁, subkey_hi32, hk.sched]
    · exact e₁.trans ⟨fun q hq => RegUpd.gpr_setReg_of_ne _ _ (by simpa using hq), rfl, rfl, rfl, rfl⟩
  · rename_i h
    obtain ⟨s₁, h₁, v₁, e₁⟩ := ldr_key_run r (2 * k) (by omega_using [hk52, h]) s hk
    exact ⟨s₁, h₁, by rw [v₁, subkey_lo32 _ _ (by omega_using [hk52]), hk.sched], e₁⟩

/-- A data-processing instruction with a register operand. -/
theorem dp_run (op : DpOp) (d n r : Reg) (s : State) :
    ∃ s', runBlock isa [.dp op d n (.reg r)] s = some s' ∧
      s'.gpr d = (match op with
        | .add => s.gpr n + s.gpr r | .sub => s.gpr n - s.gpr r | .and => s.gpr n &&& s.gpr r
        | .orr => s.gpr n ||| s.gpr r | .eor => s.gpr n ^^^ s.gpr r | .bic => s.gpr n &&& ~~~(s.gpr r)) ∧
      Keep [d] s s' := by
  cases op <;>
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, true_and] <;>
  keep_tac

theorem addKey_run (r : Reg) (hr : r ≠ .r12) (s : State) (hm : MaskOk s) :
    ∃ s', runBlock isa (addKey r) s = some s' ∧
      s'.gpr r = (s.gpr r + s.gpr .r9) &&& 65535 ∧ Keep [r] s s' := by
  obtain ⟨s₁, h₁, v₁, e₁⟩ := dp_run .add r r .r9 s
  obtain ⟨s₂, h₂, v₂, e₂⟩ := dp_run .and r r .r12 s₁
  refine ⟨s₂, run_append h₁ h₂, ?_, e₁.trans e₂⟩
  simp only at v₁ v₂
  rw [v₂, v₁, e₁.reg .r12 (by simpa using Ne.symm hr), hm]

/-- The six subkeys of round `j`. -/
abbrev rk (z : Spec.Idea.Schedule) (j i : Nat) : Spec.Idea.Word := z.getD (6 * j + i) 0

/-- The written registers of a round. -/
abbrev roundWrites : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem round_run (j : Nat) (hj : j < 8) (b c : Reg)
    (hb : (b == .r5 && c == .r6 || b == .r6 && c == .r5) = true)
    (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x b c s) (hk : KeyOk z s)
    (hm : MaskOk s) :
    ∃ s', runBlock isa (roundWith j b c) s = some s' ∧
      Holds (Spec.Idea.round (rk z j 0) (rk z j 1) (rk z j 2) (rk z j 3) (rk z j 4) (rk z j 5) x)
        c b s' ∧
      Keep roundWrites s s' := by
  -- What the two registers are not.
  obtain nb : ∀ r ∈ [Reg.r0, .r4, .r7, .r8, .r9, .r10, .r11, .r12], b ≠ r ∧ c ≠ r := by
    intro r hr
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hbc : b ≠ c := by
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide
  obtain hsub : ∀ r ∈ [b, c], r ∈ roundWrites := by
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide
  obtain ⟨b0, c0⟩ := nb .r0 (by simp)
  obtain ⟨b4, c4⟩ := nb .r4 (by simp)
  obtain ⟨b7, c7⟩ := nb .r7 (by simp)
  obtain ⟨b8, c8⟩ := nb .r8 (by simp)
  obtain ⟨b9, c9⟩ := nb .r9 (by simp)
  obtain ⟨b10, c10⟩ := nb .r10 (by simp)
  obtain ⟨b11, c11⟩ := nb .r11 (by simp)
  obtain ⟨b12, c12⟩ := nb .r12 (by simp)
  obtain kb : ∀ {rs : List Reg} {s s' : State}, Keep rs s s' →
      (∀ r ∈ rs, r ∈ [Reg.r4, .r7, .r8, .r9, .r10, .r11]) → s'.gpr b = s.gpr b ∧ s'.gpr c = s.gpr c :=
    fun {rs s s'} e h => ⟨e.reg b fun hm => by
        rcases List.mem_cons.mp (h b hm) with h' | h' <;> simp_all,
      e.reg c fun hm => by rcases List.mem_cons.mp (h c hm) with h' | h' <;> simp_all⟩
  obtain r12 : ∀ {rs : List Reg} {s s' : State}, Keep rs s s' → .r12 ∉ rs → MaskOk s → MaskOk s' :=
    fun e h hm => (e.reg .r12 h).trans hm
  -- X₁ ⊙ Z₁
  obtain ⟨s₁, h₁, v₁, e₁⟩ := loadKey_run .r9 (6 * j) (by omega_using [hj]) s hk
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mul_run .r4 .r4 .r9 (by decide) s₁ (r12 e₁ (by decide) hm)
  -- X₄ ⊙ Z₄
  obtain ⟨s₃, h₃, v₃, e₃⟩ := loadKey_run .r9 (6 * j + 3) (by omega_using [hj]) s₂
    ((hk.keep e₁ (by decide)).keep e₂ (by decide))
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mul_run .r7 .r7 .r9 (by decide) s₃
    (r12 e₃ (by decide) (r12 e₂ (by decide) (r12 e₁ (by decide) hm)))
  obtain e₀₄ : Keep [.r4, .r7, .r8, .r9] s s₄ :=
    (((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))).trans
      (e₄.weaken (by decide))
  obtain k₄ : KeyOk z s₄ := hk.keep e₀₄ (by decide)
  obtain m₄ : MaskOk s₄ := r12 e₀₄ (by decide) hm
  -- X₂ ⊞ Z₂, X₃ ⊞ Z₃
  obtain ⟨s₅, h₅, v₅, e₅⟩ := loadKey_run .r9 (6 * j + 1) (by omega_using [hj]) s₄ k₄
  obtain ⟨s₆, h₆, v₆, e₆⟩ := addKey_run b b12 s₅ (r12 e₅ (by decide) m₄)
  obtain ⟨s₇, h₇, v₇, e₇⟩ := loadKey_run .r9 (6 * j + 2) (by omega_using [hj]) s₆
    ((k₄.keep e₅ (by decide)).keep e₆ (by simpa using b0.symm))
  obtain ⟨s₈, h₈, v₈, e₈⟩ := addKey_run c c12 s₇
    (r12 e₇ (by decide) (r12 e₆ (by simpa using b12.symm) (r12 e₅ (by decide) m₄)))
  obtain e₄₈ : Keep [.r9, b, c] s₄ s₈ :=
    (((e₅.mono (by simp)).trans (e₆.mono (by simp))).trans (e₇.mono (by simp))).trans
      (e₈.mono (by simp))
  obtain k₈ : KeyOk z s₈ := k₄.keep e₄₈ (by simp [b0.symm, c0.symm])
  obtain m₈ : MaskOk s₈ := r12 e₄₈ (by simp [b12.symm, c12.symm]) m₄
  -- t₀
  obtain ⟨s₉, h₉, v₉, e₉⟩ := dp_run .eor .r10 .r4 c s₈
  obtain ⟨s₁₀, h₁₀, v₁₀, e₁₀⟩ := loadKey_run .r9 (6 * j + 4) (by omega_using [hj]) s₉ (k₈.keep e₉ (by decide))
  obtain ⟨s₁₁, h₁₁, v₁₁, e₁₁⟩ := mul_run .r10 .r10 .r9 (by decide) s₁₀
    (r12 e₁₀ (by decide) (r12 e₉ (by decide) m₈))
  -- t₁
  obtain ⟨s₁₂, h₁₂, v₁₂, e₁₂⟩ := dp_run .eor .r11 b .r7 s₁₁
  obtain ⟨s₁₃, h₁₃, v₁₃, e₁₃⟩ := dp_run .add .r11 .r11 .r10 s₁₂
  obtain e₈₁₃ : Keep [.r8, .r9, .r10, .r11] s₈ s₁₃ :=
    ((((e₉.weaken (by decide)).trans (e₁₀.weaken (by decide))).trans (e₁₁.weaken (by decide))).trans
      (e₁₂.weaken (by decide))).trans (e₁₃.weaken (by decide))
  obtain ⟨s₁₄, h₁₄, v₁₄, e₁₄⟩ := loadKey_run .r9 (6 * j + 5) (by omega_using [hj]) s₁₃ (k₈.keep e₈₁₃ (by decide))
  obtain ⟨s₁₅, h₁₅, v₁₅, e₁₅⟩ := mul_run .r11 .r11 .r9 (by decide) s₁₄
    (r12 e₁₄ (by decide) (r12 e₈₁₃ (by decide) m₈))
  -- The outputs.
  obtain ⟨s₁₆, h₁₆, v₁₆, e₁₆⟩ := dp_run .add .r10 .r10 .r11 s₁₅
  obtain ⟨s₁₇, h₁₇, v₁₇, e₁₇⟩ := dp_run .and .r10 .r10 .r12 s₁₆
  obtain ⟨s₁₈, h₁₈, v₁₈, e₁₈⟩ := dp_run .eor .r4 .r4 .r11 s₁₇
  obtain ⟨s₁₉, h₁₉, v₁₉, e₁₉⟩ := dp_run .eor c c .r11 s₁₈
  obtain ⟨s₂₀, h₂₀, v₂₀, e₂₀⟩ := dp_run .eor b b .r10 s₁₉
  obtain ⟨s₂₁, h₂₁, v₂₁, e₂₁⟩ := dp_run .eor .r7 .r7 .r10 s₂₀
  simp only at v₉ v₁₂ v₁₃ v₁₆ v₁₇ v₁₈ v₁₉ v₂₀ v₂₁
  refine ⟨s₂₁, ?_, ?_, ?_⟩
  · simp only [roundWith]
    obtain t : runBlock isa ([.dp .add .r10 .r10 (.reg .r11), .dp .and .r10 .r10 (.reg .r12),
        .dp .eor .r4 .r4 (.reg .r11), .dp .eor c c (.reg .r11),
        .dp .eor b b (.reg .r10), .dp .eor .r7 .r7 (.reg .r10)] : List Instr) s₁₅ = some s₂₁ :=
      run_append h₁₆ (run_append h₁₇ (run_append h₁₈ (run_append h₁₉ (run_append h₂₀ h₂₁))))
    obtain m : runBlock isa ([.dp .eor .r11 b (.reg .r7), .dp .add .r11 .r11 (.reg .r10)] : List Instr) s₁₁ =
        some s₁₃ := run_append h₁₂ h₁₃
    exact run_append (run_append (run_append (run_append (run_append (run_append (run_append
      (run_append (run_append (run_append (run_append (run_append (run_append (run_append
      h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉) h₁₀) h₁₁) m) h₁₄) h₁₅) t
  · -- The values, from the last write back.
    obtain a : s₈.gpr .r4 = (Spec.Idea.mul (x.getD 0 0) (rk z j 0)).setWidth 32 := by
      rw [e₄₈.reg .r4 (by simp [b4.symm, c4.symm]), e₄.reg .r4 (by decide), e₃.reg .r4 (by decide), v₂,
        e₁.reg .r4 (by decide), hx.r4, setWidth_setWidth16_32, v₁]
      rfl
    obtain d : s₈.gpr .r7 = (Spec.Idea.mul (x.getD 3 0) (rk z j 3)).setWidth 32 := by
      rw [e₄₈.reg .r7 (by simp [b7.symm, c7.symm]), v₄, v₃, e₃.reg .r7 (by decide),
        e₂.reg .r7 (by decide), e₁.reg .r7 (by decide), hx.r7, setWidth_setWidth16_32]
    obtain bv : s₈.gpr b = (x.getD 1 0 + rk z j 1).setWidth 32 := by
      obtain hb₄ := (kb e₀₄ (by decide)).1
      rw [e₈.reg b (by simpa using hbc), e₇.reg b (by simpa using b9), v₆, e₅.reg b (by simpa using b9),
        hb₄, hx.b, add_mask32, v₅]
    obtain cv : s₈.gpr c = (x.getD 2 0 + rk z j 2).setWidth 32 := by
      obtain hc₄ := (kb e₀₄ (by decide)).2
      rw [v₈, e₇.reg c (by simpa using c9), e₆.reg c (by simpa using Ne.symm hbc),
        e₅.reg c (by simpa using c9), hc₄, hx.c, add_mask32, v₇]
    obtain t₀ : s₁₁.gpr .r10 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^
        (x.getD 2 0 + rk z j 2)) (rk z j 4)).setWidth 32 := by
      rw [v₁₁, e₁₀.reg .r10 (by decide), v₉, a, cv, xor_setWidth32, setWidth_setWidth16_32, v₁₀]
    obtain keep₁₅ : ∀ r ∈ [Reg.r4, .r7], s₁₅.gpr r = s₈.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact (e₁₅.reg _ (by decide)).trans ((e₁₄.reg _ (by decide)).trans (e₈₁₃.reg _ (by decide)))
    obtain kbc₁₅ := kb ((e₈₁₃.trans (e₁₄.weaken (by decide))).trans (e₁₅.weaken (by decide))) (by decide)
    obtain t₁ : s₁₅.gpr .r11 = (Spec.Idea.mul (((x.getD 1 0 + rk z j 1) ^^^
        Spec.Idea.mul (x.getD 3 0) (rk z j 3)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^ (x.getD 2 0 + rk z j 2)) (rk z j 4))
        (rk z j 5)).setWidth 32 := by
      rw [v₁₅, e₁₄.reg .r11 (by decide), v₁₃, v₁₂, e₁₂.reg .r10 (by decide), t₀,
        e₁₁.reg b (by simp [b8, b9, b10]), e₁₀.reg b (by simpa using b9),
        e₉.reg b (by simpa using b10), bv,
        e₁₁.reg .r7 (by decide), e₁₀.reg .r7 (by decide), e₉.reg .r7 (by decide), d,
        xor_setWidth32, add_setWidth32, v₁₄]
    obtain kbc₁₇ := kb ((e₁₆.weaken (rs' := [.r10]) (by decide)).trans (e₁₇.weaken (by decide))) (by decide)
    obtain r10₁₅ : s₁₅.gpr .r10 = s₁₁.gpr .r10 := by
      rw [e₁₅.reg .r10 (by decide), e₁₄.reg .r10 (by decide), e₁₃.reg .r10 (by decide)]
      · exact e₁₂.reg .r10 (by decide)
    obtain r10₁₇ : s₁₇.gpr .r10 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^
        (x.getD 2 0 + rk z j 2)) (rk z j 4) + Spec.Idea.mul (((x.getD 1 0 + rk z j 1) ^^^
        Spec.Idea.mul (x.getD 3 0) (rk z j 3)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^ (x.getD 2 0 + rk z j 2)) (rk z j 4))
        (rk z j 5)).setWidth 32 := by
      rw [v₁₇, v₁₆, e₁₆.reg .r12 (by decide), e₁₅.reg .r12 (by decide), e₁₄.reg .r12 (by decide),
        e₈₁₃.reg .r12 (by decide), m₈, r10₁₅, t₀, t₁, add_mask32, setWidth_setWidth16_32]
    obtain r11₁₇ : s₁₇.gpr .r11 = s₁₅.gpr .r11 := by
      rw [e₁₇.reg .r11 (by decide), e₁₆.reg .r11 (by decide)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e₂₁.reg .r4 (by decide), e₂₀.reg .r4 (by simpa using b4.symm), e₁₉.reg .r4 (by simpa using c4.symm),
        v₁₈, e₁₇.reg .r4 (by decide), e₁₆.reg .r4 (by decide), keep₁₅ .r4 (by simp), a, r11₁₇, t₁,
        xor_setWidth32]
      rfl
    · rw [e₂₁.reg c (by simpa using c7), e₂₀.reg c (by simpa using Ne.symm hbc), v₁₉,
        e₁₈.reg c (by simpa using c4), e₁₈.reg .r11 (by decide), kbc₁₇.2, kbc₁₅.2, cv, r11₁₇, t₁,
        xor_setWidth32]
      rfl
    · rw [e₂₁.reg b (by simpa using b7), v₂₀, e₁₉.reg b (by simpa using hbc), e₁₈.reg b (by simpa using b4),
        e₁₉.reg .r10 (by simpa using c10.symm), e₁₈.reg .r10 (by decide), kbc₁₇.1, kbc₁₅.1, bv, r10₁₇,
        xor_setWidth32]
      rfl
    · rw [v₂₁, e₂₀.reg .r7 (by simpa using b7.symm), e₁₉.reg .r7 (by simpa using c7.symm),
        e₁₈.reg .r7 (by decide), e₂₀.reg .r10 (by simpa using b10.symm),
        e₁₉.reg .r10 (by simpa using c10.symm), e₁₈.reg .r10 (by decide), r10₁₇,
        e₁₇.reg .r7 (by decide), e₁₆.reg .r7 (by decide), keep₁₅ .r7 (by simp), d, xor_setWidth32]
      rfl
  · have hB : ∀ r ∈ [b], r ∈ roundWrites := fun r hr => hsub r (by simp at hr; simp [hr])
    obtain hC : ∀ r ∈ [c], r ∈ roundWrites := fun r hr => hsub r (by simp at hr; simp [hr])
    obtain e₄₈' : Keep roundWrites s₄ s₈ := e₄₈.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · decide
      · exact hB _ (by simp)
      · exact hC _ (by simp)
    exact ((((((((((e₀₄.weaken (by decide)).trans e₄₈').trans (e₈₁₃.weaken (by decide))).trans
      (e₁₄.weaken (by decide))).trans (e₁₅.weaken (by decide))).trans (e₁₆.weaken (by decide))).trans
      (e₁₇.weaken (by decide))).trans (e₁₈.weaken (by decide))).trans (e₁₉.mono hC)).trans
      (e₂₀.mono hB)).trans (e₂₁.weaken (by decide))

end VG.Proof.Idea.Arm

end

end

/-!
# IDEA on ARMv7: a block

`cryptBlock_run`: `Impl.Idea.Arm.cryptBlock` replaces the block at `r1` with
`Spec.Idea.cryptBlock` of it under the subkeys at `r0`, writing no register
but `r4`–`r12`: the interface a mode reuses it through.
-/

@[expose] public section

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
  rw [addr_add (by have := h.fit; omega_using [hk, this]), h.addr]

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
  have h0 := hb (2 * k) (by omega_using [hk])
  have h1 := hb (2 * k + 1) (by omega_using [hk])
  simp only [loadWord, runBlock_cons, runStep_some, runBlock_nil, isa, exec, State.load8, Op2.eval,
    show 2 * k < 4096 by omega_using [hk], show 2 * k + 1 < 4096 by omega_using [hk], ↓reduceIte,
    ha.off (k := 2 * k) (by omega_using [hk]), ha.off (k := 2 * k + 1) (by omega_using [hk]), h0, h1,
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
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h, show (n + 1) % 2 = 0 ↔ ¬ n % 2 = 0 by omega_using []]

theorem regC_succ (n : Nat) : regC (n + 1) = regB n := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h, show (n + 1) % 2 = 0 ↔ ¬ n % 2 = 0 by omega_using []]

theorem regBC_ok (n : Nat) : (regB n == .r5 && regC n == .r6 || regB n == .r6 && regC n == .r5) = true := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h]

theorem rounds_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) :
    ∀ n ≤ 8, ∀ s : State, Holds x .r5 .r6 s → KeyOk z s → MaskOk s →
      ∃ s', runBlock isa ((List.range n).flatMap round) s = some s' ∧
        Holds (roundsSpec z n x) (regB n) (regC n) s' ∧ Keep roundWrites s s'
  | 0, _, s, hx, _, _ => ⟨s, by simp [runBlock_nil], hx, Keep.refl _ _⟩
  | n + 1, hn, s, hx, hk, hm => by
    obtain ⟨s₁, h₁, x₁, e₁⟩ := rounds_run z x n (by omega_using [hn]) s hx hk hm
    obtain ⟨s₂, h₂, x₂, e₂⟩ := round_run n (by omega_using [hn]) (regB n) (regC n) (regBC_ok n) z _ s₁ x₁
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
  have h0 := hw (2 * k) (by omega_using [hk])
  have h1 := hw (2 * k + 1) (by omega_using [hk])
  simp only [storeWord, runBlock_cons, runStep_some, runBlock_nil, isa, exec, State.store8, Op2.eval,
    show 2 * k < 4096 by omega_using [hk], show 2 * k + 1 < 4096 by omega_using [hk], ↓reduceIte, h0, h1,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, Nat.reduceLeDiff, and_self,
    reduceCtorEq, ha.off (k := 2 * k) (by omega_using [hk]), ha.off (k := 2 * k + 1) (by omega_using [hk]),
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q hq => ite_eq_right hq, rfl, trivial, rfl⟩

theorem frame_write8 {a : Addr} {m m' : Mem} {j : Nat} (v : BitVec 8) (hj : j < 8)
    (h : Frame [⟨a, 8⟩] m m') : Frame [⟨a, 8⟩] m (m'.writeW (a + BitVec.ofNat 64 j) v) :=
  h.writeW (List.mem_singleton_self _) v (Offset.contains_base a (by omega_using [hj]) (by omega_using [hj]))

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
        i = 5 ∨ i = 6 ∨ i = 7 := by omega_using [hi]
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

end

end

/-! ### `Idea.Arm.Ecb`, which only this module used -/

section

/-!
# IDEA ECB on ARMv7

`ecb_wp`: with the scratch buffer as an argument (at `r3`, 32 bytes),
`Impl.Idea.Arm.ecb` saves `r4`–`r11` in it, transforms the blocks in a loop
(`loop_ok`) whose invariant (`LoopInv`) says how many remain, that the ones
before are transformed and the ones after not yet (each iteration is
`cryptBlock_run`), and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Arm.Spill VG.Impl.Idea.Arm

/-! ## The loop -/

theorem advance_run (s : State) :
    ∃ s', runBlock isa [.dp .add .r1 .r1 (.imm 8), .subs .r2 .r2 (.imm 1)] s = some s' ∧
      s'.gpr .r1 = s.gpr .r1 + 8 ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
      Keep [.r1, .r2] s s' := by
  obtain e8 : encodable 8 = true := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, e8, enc_one, ↓reduceIte,
    Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, Option.some.injEq, exists_eq_left', true_and]
  refine ⟨rfl, rfl, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  show (if q = .r2 then _ else (subFlags (s.setReg .r1 _) _ _).gpr q) = _
  simp only [hq.2, ite_false]
  exact RegUpd.gpr_setReg_of_ne _ _ hq.1

/-- The registers the loop writes. -/
abbrev loopWrites : List Reg := [.r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The facts about the state `o` before the loop that the loop relies on:
the schedule `z` at `r0`, readable, and `n` blocks at `r1` (address `A`),
writable, apart from it, neither wrapping around. -/
structure LoopCtx (z : Spec.Idea.Schedule) (A : Addr) (n : Nat) (o : State) : Prop where
  sched : ⟨State.addr (o.gpr .r0), 104⟩ ∈ o.rd ++ o.wr
  fit0 : (o.gpr .r0).toNat + 104 ≤ 2 ^ 32
  data : ⟨A, 8 * n⟩ ∈ o.wr
  z : Spec.Idea.scheduleAt o.mem (State.addr (o.gpr .r0)) = z
  sep : (⟨State.addr (o.gpr .r0), 104⟩ : Region).Disjoint ⟨A, 8 * n⟩
  addr : State.addr (o.gpr .r1) = A
  fit1 : (o.gpr .r1).toNat + 8 * n ≤ 2 ^ 32

/-- `r` blocks remain, from block `n - r` on: the ones before are transformed. -/
structure LoopInv (z : Spec.Idea.Schedule) (A : Addr) (n : Nat) (m₀ : Mem) (o : State) (r : Nat)
    (t : State) : Prop where
  pos : 1 ≤ r
  le : r ≤ n
  r1 : t.gpr .r1 = o.gpr .r1 + BitVec.ofNat 32 (8 * (n - r))
  r2 : t.gpr .r2 = BitVec.ofNat 32 r
  keep : Keep loopWrites o { t with mem := o.mem }
  frame : Frame [⟨A, 8 * n⟩] o.mem t.mem
  done : ∀ j < n - r, Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j)))
  todo : ∀ j, n - r ≤ j → j < n → Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j))

/-- After the loop: every block transformed. -/
structure LoopPost (z : Spec.Idea.Schedule) (A : Addr) (n : Nat) (m₀ : Mem) (o : State)
    (t : State) : Prop where
  keep : Keep loopWrites o { t with mem := o.mem }
  frame : Frame [⟨A, 8 * n⟩] o.mem t.mem
  done : ∀ j < n, Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j)))

theorem step_ok {z : Spec.Idea.Schedule} {A : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z A n o) (r : Nat) (t : State) (hi : LoopInv z A n m₀ o r t) :
    WP isa (.block (cryptBlock ++ ([.dp .add .r1 .r1 (.imm 8), .subs .r2 .r2 (.imm 1)] : List Instr))) t
      (fun t' => (isa.eval .ne t' = some false ∧ LoopPost z A n m₀ o t') ∨
        (isa.eval .ne t' = some true ∧ ∃ r' < r, LoopInv z A n m₀ o r' t')) := by
  have hrd : t.rd = o.rd := hi.keep.rd
  have hwr : t.wr = o.wr := hi.keep.wr
  obtain hr0 : t.gpr .r0 = o.gpr .r0 := hi.keep.reg .r0 (by decide)
  obtain hj : n - r < n := by have := hi.pos; have := hi.le; omega_arith
  obtain hb64 : 8 * n ≤ 2 ^ 64 := by have := hc.fit1; omega_arith
  obtain hfit : (o.gpr .r1).toNat + 8 * (n - r) < 2 ^ 32 := by have := hc.fit1; omega_arith
  obtain hr1n : (t.gpr .r1).toNat = (o.gpr .r1).toNat + 8 * (n - r) := by
    rw [hi.r1, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * (n - r)) (by omega_arith),
      Nat.mod_eq_of_lt hfit]
  obtain hat : BlockAt t (A + BitVec.ofNat 64 (8 * (n - r))) :=
    ⟨by rw [hi.r1, addr_add hfit, hc.addr], by rw [hr1n]; have := hc.fit1; omega_arith⟩
  obtain hread : BlockRead t (A + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hrd, hwr]; exact List.mem_append_right _ hc.data,
      block_contains hj (by omega_arith) (by decide) hb64⟩
  obtain hwrite : BlockWrite t (A + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hwr]; exact hc.data, block_contains hj (by omega_arith) (by decide) hb64⟩
  obtain hk : KeyOk z t := by
    refine ⟨by rw [hr0, hrd, hwr]; exact hc.sched, by rw [hr0]; exact hc.fit0, ?_⟩
    rw [hr0, ← hc.z]
    exact scheduleAt_congr (frame_bytes hi.frame (by simpa using hc.sep) (by decide))
  obtain ⟨t₁, h₁, b₁, f₁, g₁, rd₁, wr₁, sp₁⟩ := cryptBlock_run z t hat hread hwrite hk
  obtain ⟨t₂, h₂, r1₂, r2₂, z₂, e₂⟩ := advance_run t₁
  refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_⟩
  obtain keep₂ : Keep loopWrites o { t₂ with mem := o.mem } := by
    refine ⟨fun q hq => ?_, rfl, ?_, ?_, ?_⟩
    · show t₂.gpr q = o.gpr q
      obtain s₁ : ∀ q, q ∈ [Reg.r1, .r2] → q ∈ loopWrites := by decide
      obtain s₂ : ∀ q, q ∈ blockWrites → q ∈ loopWrites := by decide
      rw [e₂.reg q (fun h => hq (s₁ q h)), g₁ q (fun h => hq (s₂ q h))]
      exact hi.keep.reg q hq
    · show t₂.rd = o.rd; rw [e₂.rd, rd₁, hrd]
    · show t₂.wr = o.wr; rw [e₂.wr, wr₁, hwr]
    · show t₂.sp = o.sp; rw [e₂.sp, sp₁]; exact hi.keep.sp
  have mem₂ : t₂.mem = t₁.mem := e₂.mem
  obtain frame₂ : Frame [⟨A, 8 * n⟩] o.mem t₂.mem := by
    rw [mem₂]
    refine hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base A (by omega_arith)
  have other (j : Nat) (hjn : j < n) (hne : j ≠ n - r) :
      Spec.Idea.blockAt t₂.mem (A + BitVec.ofNat 64 (8 * j)) =
        Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) := by
    rw [mem₂]
    exact blockAt_congr (frame_bytes f₁ (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact blocks_disjoint hj hjn (Ne.symm hne) hb64) (by decide))
  obtain done₂ : ∀ j < n - (r - 1), Spec.Idea.blockAt t₂.mem (A + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j))) := by
    intro j hjr
    by_cases he : j = n - r
    · subst he
      rw [mem₂, b₁, hi.todo _ (Nat.le_refl _) hj]
    · rw [other j (by omega_arith) he]
      exact hi.done j (by have := hi.pos; omega_arith)
  obtain hn32 : n < 2 ^ 32 := by have := hc.fit1; omega_arith
  obtain hr2 : t₂.gpr .r2 = BitVec.ofNat 32 (r - 1) := by
    rw [r2₂, g₁ .r2 (by decide), hi.r2]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  obtain hev : isa.eval .ne t₂ = some (decide (r - 1 ≠ 0)) := by
    show some (!t₂.z) = _
    rw [z₂, ← r2₂, hr2]
    congr 1
    by_cases h0 : r - 1 = 0
    · simp only [h0]; rfl
    · have hne : BitVec.ofNat 32 (r - 1) ≠ 0 := fun h => h0 (by
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hi.le; omega_arith)] at this
        exact this)
      rw [show (BitVec.ofNat 32 (r - 1) == 0) = false from by simpa using hne]
      simp [h0]
  by_cases hlast : r = 1
  · subst hlast
    left
    exact ⟨hev, keep₂, frame₂, fun j hjn => done₂ j (by omega_arith)⟩
  · right
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega_arith,
      r - 1, by have := hi.pos; omega_arith, ?_⟩
    refine ⟨by have := hi.pos; omega_arith, by have := hi.le; omega_arith, ?_, hr2, keep₂, frame₂, done₂, ?_⟩
    · rw [r1₂, g₁ .r1 (by decide), hi.r1]
      apply BitVec.eq_of_toNat_eq
      have := hi.pos; have := hi.le; have := hc.fit1
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (8 : BitVec 32).toNat = 8 from rfl, Nat.mod_eq_of_lt (a := 8 * (n - r)) (by omega_arith),
        Nat.mod_eq_of_lt (a := 8 * (n - (r - 1))) (by omega_arith), Nat.mod_eq_of_lt hfit,
        show 8 * (n - (r - 1)) = 8 * (n - r) + 8 by omega_arith, Nat.add_assoc]
    · intro j hj₁ hj₂
      have := hi.pos
      have := hi.le
      obtain hne : j ≠ n - r := by omega_arith
      rw [other j hj₂ hne]
      exact hi.todo j (by omega_arith) hj₂

end VG.Proof.Idea.Arm

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Arm.Spill VG.Impl.Idea.Arm

theorem loop_ok {z : Spec.Idea.Schedule} {A : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z A n o) (hn : 1 ≤ n) (hr2 : o.gpr .r2 = BitVec.ofNat 32 n)
    (htodo : ∀ j < n, Spec.Idea.blockAt o.mem (A + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j))) :
    WP isa (.loop (.block (cryptBlock ++ ([.dp .add .r1 .r1 (.imm 8), .subs .r2 .r2 (.imm 1)] : List Instr)))
      .ne) o (LoopPost z A n m₀ o) := by
  refine WP.loop (M := isa) (LoopInv z A n m₀ o) (fun r t hi => step_ok hc r t hi) n o
    ⟨hn, Nat.le_refl _, ?_, hr2, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, Frame.refl _ _,
      fun j hj => by omega_arith, fun j _ hj => htodo j hj⟩
  rw [Nat.sub_self, Nat.mul_zero]; exact (BitVec.add_zero _).symm

/-! ## The function -/

/-- The ECB contract on ARMv7, with the scratch buffer (32 bytes) at `r3`. -/
def contract : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 104⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 32⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧
      (s.gpr .r0).toNat + 104 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 32 ≤ 2 ^ 32
  post s s' := Spec.Idea.blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
    Spec.Idea.ecb (Spec.Idea.scheduleAt s.mem (State.addr (s.gpr .r0)))
      (Spec.Idea.blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub := PublicRegs [.r0, .r1, .r2, .r3]

/-- What the loop (or no loop) leaves, before the registers are restored. -/
structure Mid (z : Spec.Idea.Schedule) (A : Addr) (n : Nat) (m₀ : Mem) (o t : State) : Prop where
  keep : Keep loopWrites o { t with mem := o.mem }
  frame : Frame [⟨A, 8 * n⟩] o.mem t.mem
  done : ∀ j < n, Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j)))

theorem ecb_wp (s : State) (hs : contract.pre s) :
    WP isa ecb s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, fit0, fit1, fit3⟩ := hs
  obtain hb64 : 8 * (s.gpr .r2).toNat ≤ 2 ^ 64 := by omega_arith
  obtain hslots : Slots 0 32 ecbSaved := by decide
  obtain hinS : ∀ d, 0 ≤ d → d + 4 ≤ 32 → InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 d) 4 :=
    fun d _ h => ⟨⟨State.addr (s.gpr .r3), 32⟩, by rw [hwr]; simp, Offset.contains_base _ h (by omega_arith)⟩
  unfold ecb
  refine WP.seq (save_slots_ok hslots fit3 hinS ?_)
  -- After saving.
  obtain hf₁ : Frame [⟨State.addr (s.gpr .r3), 32⟩] s.mem
      (saveMem s.mem (State.addr (s.gpr .r3)) s.gpr ecbSaved) :=
    saveMem_frame _ _ _ (by decide) _ (by decide)
  obtain hsv₁ := saveMem_saved (State.addr (s.gpr .r3)) s.gpr s.mem ecbSaved hslots
  generalize saveMem s.mem (State.addr (s.gpr .r3)) s.gpr ecbSaved = M₁ at hf₁ hsv₁
  -- `cmp r2, #0`.
  obtain e0 : encodable 0 = true := by decide
  refine WP.of_runBlock ⟨subFlags { s with mem := M₁ } (s.gpr .r2) 0, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, e0, ↓reduceIte,
      Option.map_some], ?_⟩
  generalize hs₂ : subFlags { s with mem := M₁ } (s.gpr .r2) 0 = s₂
  obtain g₂ : s₂.gpr = s.gpr := by rw [← hs₂]; rfl
  obtain mem₂ : s₂.mem = M₁ := by rw [← hs₂]; rfl
  obtain rd₂ : s₂.rd = s.rd := by rw [← hs₂]; rfl
  obtain wr₂ : s₂.wr = s.wr := by rw [← hs₂]; rfl
  obtain z₂ : s₂.z = (s.gpr .r2 - 0 == 0) := by rw [← hs₂]; rfl
  let z := Spec.Idea.scheduleAt s.mem (State.addr (s.gpr .r0))
  let A := State.addr (s.gpr .r1)
  let n := (s.gpr .r2).toNat
  obtain blocks₂ : ∀ j < n, Spec.Idea.blockAt s₂.mem (A + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt s.mem (A + BitVec.ofNat 64 (8 * j)) := fun j hj => by
    rw [mem₂]
    exact blockAt_congr (frame_bytes hf₁ (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact dDS.sub_left (Offset.sub_base A (by omega_arith))) (by decide))
  refine WP.seq (WP.mono (Q := Mid z A n s.mem s₂) ?_ fun t ht => ?_)
  · -- The blocks.
    obtain hz : isa.eval .eq s₂ = some (decide (n = 0)) := by
      show some s₂.z = _
      rw [z₂, show s.gpr .r2 - 0 = s.gpr .r2 from BitVec.sub_zero _]
      congr 1
    refine WP.ite _ hz (fun h0 => ?_) (fun h0 => ?_)
    · have h0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, Frame.refl _ _, fun j hj => by omega_arith⟩
    · have h0 : n ≠ 0 := by simpa using h0
      obtain ctx : LoopCtx z A n s₂ := by
        refine ⟨?_, by rw [g₂]; exact fit0, by rw [wr₂, hwr]; simp [A, n], ?_, ?_, by rw [g₂],
          by rw [g₂]; exact fit1⟩
        · rw [g₂, rd₂, hrd]; simp
        · rw [g₂, mem₂]
          exact scheduleAt_congr (frame_bytes hf₁ (by
            intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact dSS) (by decide))
        · rw [g₂]; exact dSD
      refine WP.mono (loop_ok ctx (Nat.pos_of_ne_zero h0) (by rw [g₂]; simp [n]) blocks₂)
        fun t ht => ⟨ht.keep, ht.frame, ht.done⟩
  · -- Restoring the registers.
    obtain r3t : t.gpr .r3 = s.gpr .r3 := (ht.keep.reg .r3 (by decide)).trans (by rw [g₂])
    obtain hsv : Saved t.mem (State.addr (t.gpr .r3)) s.gpr ecbSaved := by
      rw [r3t]
      refine hsv₁.frame hslots (mem₂ ▸ ht.frame) fun q hq => ?_
      simp only [List.mem_singleton] at hq; subst hq
      rw [BitVec.add_zero]
      exact dDS.symm
    obtain hin : ∀ d, 0 ≤ d → d + 4 ≤ 32 →
        InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r3) + BitVec.ofNat 64 d) 4 := fun d h0 h => by
      obtain ⟨R, hR, hc⟩ := hinS d h0 h
      rw [ht.keep.rd, ht.keep.wr, rd₂, wr₂, r3t]
      exact ⟨R, List.mem_append_right _ hR, hc⟩
    refine WP.mono (restore_block_ok hslots (by decide) (by rw [r3t]; exact fit3) hin hsv)
      fun u hu' => ?_
    obtain ⟨hu, ho, hm, -⟩ := hu'
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hu (.r4, 0) (by decide)
      · exact hu (.r5, 4) (by decide)
      · exact hu (.r6, 8) (by decide)
      · exact hu (.r7, 12) (by decide)
      · exact hu (.r8, 16) (by decide)
      · exact hu (.r9, 20) (by decide)
      · exact hu (.r10, 24) (by decide)
      · exact hu (.r11, 28) (by decide)
      · rw [ho .lr (by decide)]
        exact (ht.keep.reg .lr (by decide)).trans (by rw [g₂])
    · show Spec.Idea.blocksAt u.mem _ _ = _
      rw [hm]
      exact blocksAt_eq _ _ _ _ _ ht.done

theorem ecb_correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa ecb s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_wp s hs
  exact ⟨t, s', he, ⟨ha, Exec.sp he⟩, hp⟩

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 1 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 32⟩]

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.r0, .r1, .r2, .r3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 := by
  simp [PublicRegs]

theorem ecb_verified : Verified target ecb (Proof.Idea.ecbScratchContract32 abi 8) := by
  refine Verified.of_correct ecb_correct (ecb_constantTime _) ?_
  sig_implies [Proof.Idea.ecbScratchContract32, Proof.Idea.ecbScratchSig32, Spec.Idea.ecbPost, abi,
    argRegs, reduceClassify, Loc.val, State.addr, contract, publicRegs_four] [satState] using satState

end VG.Proof.Idea.Arm

end

end

/-! ### `Idea.Arm.Invert`, which only this module used -/

section

/-!
# IDEA decryption subkeys on ARMv7

With the scratch buffer as an argument (at `r2`, 24 bytes), `invertKey`
saves `r4`–`r9` in it and restores them at the end. Each decryption subkey
is a copy, the negation or the inverse of an encryption subkey
(`invertKey_getD`, `Impl.Idea.invOp`), computed into `r3` (`invWord_ok`;
the inverse by a loop of fifteen steps of `t := (t ⊙ t) ⊙ a`,
`invLoop_ok`), placed in its 16 bits of `r7` (`invPlace`), and stored two
at a time (`invPair_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Arm.Spill VG.Impl.Idea.Arm VG.Impl.Idea

/-- The registers computing a decryption subkey writes. -/
abbrev invWrites : List Reg := [.r3, .r4, .r5, .r6, .r8, .r9]

theorem invStep_run (t : State) (hm : MaskOk t) :
    ∃ t', runBlock isa invStep t = some t' ∧
      t'.gpr .r5 = (Spec.Idea.mul (Spec.Idea.mul ((t.gpr .r5).setWidth 16) ((t.gpr .r5).setWidth 16))
        ((t.gpr .r4).setWidth 16)).setWidth 32 ∧
      t'.gpr .r6 = t.gpr .r6 - 1 ∧ t'.z = (t.gpr .r6 - 1 == 0) ∧ Keep [.r5, .r6, .r8, .r9] t t' := by
  obtain ⟨t₁, h₁, v₁, e₁⟩ := mul_run .r5 .r5 .r5 (by decide) t hm
  obtain ⟨t₂, h₂, v₂, e₂⟩ := mul_run .r5 .r5 .r4 (by decide) t₁ ((e₁.reg .r12 (by decide)).trans hm)
  refine ⟨(subFlags t₂ (t₂.gpr .r6) 1).setReg .r6 (t₂.gpr .r6 - 1), ?_, ?_, ?_, ?_, ?_⟩
  · refine run_append (run_append h₁ h₂) ?_
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, enc_one, ↓reduceIte,
      Option.map_some]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]
    show t₂.gpr .r5 = _
    rw [v₂, v₁, setWidth_setWidth16_32, e₁.reg .r4 (by decide)]
  · rw [RegUpd.gpr_setReg_self, e₂.reg .r6 (by decide), e₁.reg .r6 (by decide)]
  · show (t₂.gpr .r6 - 1 == 0) = _
    rw [e₂.reg .r6 (by decide), e₁.reg .r6 (by decide)]
  · refine (e₁.weaken (by decide)).trans ((e₂.weaken (by decide)).trans
      ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [RegUpd.gpr_setReg_of_ne _ _ hq.2.1]
    rfl

/-- `c` steps remain: `r5` holds `chain a (15 - c)` in its low word. -/
structure InvLoop (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) : Prop where
  pos : 1 ≤ c
  le : c ≤ 15
  r6 : t.gpr .r6 = BitVec.ofNat 32 c
  r4 : (t.gpr .r4).setWidth 16 = a
  r5 : (t.gpr .r5).setWidth 16 = chain a (15 - c)
  keep : Keep [.r5, .r6, .r8, .r9] t₀ t

theorem invLoop_ok (a : Spec.Idea.Word) (t₀ : State) (hm : MaskOk t₀) (c : Nat) (t : State)
    (hi : InvLoop a t₀ c t) :
    WP isa (.loop (.block invStep) .ne) t (fun t' =>
      t'.gpr .r5 = (Spec.Idea.inv a).setWidth 32 ∧ Keep [.r5, .r6, .r8, .r9] t₀ t') := by
  refine WP.loop (M := isa) (InvLoop a t₀) (fun c t hi => ?_) c t hi
  obtain ⟨t', h', r5', r6', z', e'⟩ := invStep_run t ((hi.keep.reg .r12 (by decide)).trans hm)
  refine WP.of_runBlock ⟨t', h', ?_⟩
  obtain hv : t'.gpr .r5 = (chain a (15 - c + 1)).setWidth 32 := by
    rw [r5', hi.r5, hi.r4]; rfl
  obtain hc : t'.gpr .r6 = BitVec.ofNat 32 (c - 1) := by
    rw [r6', hi.r6]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  obtain hev : isa.eval .ne t' = some (decide (c - 1 ≠ 0)) := by
    show some (!t'.z) = _
    rw [z', ← r6', hc]
    congr 1
    have := hi.le
    by_cases h0 : c - 1 = 0
    · simp only [h0]; rfl
    · have hne : BitVec.ofNat 32 (c - 1) ≠ 0 := fun h => h0 (by
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
        exact this)
      rw [show (BitVec.ofNat 32 (c - 1) == 0) = false from by simpa using hne]
      simp [h0]
  obtain keep' : Keep [.r5, .r6, .r8, .r9] t₀ t' := hi.keep.trans e'
  by_cases hlast : c = 1
  · subst hlast
    left
    refine ⟨hev, ?_, keep'⟩
    rw [hv, show 15 - 1 + 1 = 15 from rfl, chain_inv]
  · right
    have := hi.pos; have := hi.le
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega_arith,
      c - 1, by omega_arith, by omega_arith, by omega_arith, hc, ?_, ?_, keep'⟩
    · rw [e'.reg .r4 (by decide)]; exact hi.r4
    · rw [hv, setWidth_setWidth16_32, show 15 - c + 1 = 15 - (c - 1) by omega_arith]

theorem invWord_ok (z : Spec.Idea.Schedule) {n : Nat} (hn : n < 52) (t : State) (hz : KeyOk z t)
    (hm : MaskOk t) :
    WP isa (invWord n) t (fun t' =>
      t'.gpr .r3 = ((Spec.Idea.invertKey z).getD n 0).setWidth 32 ∧ Keep invWrites t t') := by
  rw [invertKey_getD z hn]
  obtain hk := invOp_lt hn
  unfold invWord
  rcases hop : invOp n with ⟨op, k⟩
  rw [hop] at hk
  cases op with
  | copy =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run .r3 k hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ := dp_run .and .r3 .r3 .r12 t₁
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_, (e₁.weaken (by decide)).trans (e₂.weaken (by decide))⟩
    simp only at v₂
    rw [v₂, e₁.reg .r12 (by decide), hm, mask32_setWidth, v₁]; rfl
  | neg =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run .r3 k hk t hz
    obtain m₁ : MaskOk t₁ := (e₁.reg .r12 (by decide)).trans hm
    obtain ⟨t₂, h₂, v₂, e₂⟩ : ∃ t₂, runBlock isa [.mov .r9 (.imm 0), .dp .sub .r3 .r9 (.reg .r3),
        .dp .and .r3 .r3 (.reg .r12)] t₁ = some t₂ ∧
        t₂.gpr .r3 = (0 - t₁.gpr .r3) &&& 65535 ∧ Keep [.r3, .r9] t₁ t₂ := by
      obtain e0 : encodable 0 = true := by decide
      simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, e0, ↓reduceIte,
        Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, m₁, Option.some.injEq, exists_eq_left']
      exact ⟨trivial, by keep_tac⟩
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_, (e₁.weaken (by decide)).trans (e₂.weaken (by decide))⟩
    rw [v₂, neg_mask32, v₁]; rfl
  | inv =>
    apply WP.seq
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run .r4 k hk t hz
    obtain ⟨t₂, h₂, r4₂, r5₂, r6₂, e₂⟩ : ∃ t₂, runBlock isa [.mov .r5 (.reg .r4), .mov .r6 (.imm 15)] t₁ =
        some t₂ ∧ t₂.gpr .r4 = t₁.gpr .r4 ∧ t₂.gpr .r5 = t₁.gpr .r4 ∧ t₂.gpr .r6 = 15 ∧
        Keep [.r5, .r6] t₁ t₂ := by
      obtain e15 : encodable 15 = true := by decide
      simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, e15, ↓reduceIte,
        Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, Option.some.injEq, exists_eq_left']
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | keep_tac
    obtain m₂ : MaskOk t₂ := (e₂.reg .r12 (by decide)).trans ((e₁.reg .r12 (by decide)).trans hm)
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_⟩
    apply WP.seq
    refine WP.mono (invLoop_ok (z.getD k 0) t₂ m₂ 15 t₂ ⟨by decide, by decide, r6₂, by rw [r4₂, v₁],
      by rw [r5₂, v₁]; rfl, Keep.refl _ _⟩) fun t₃ h₃ => ?_
    obtain ⟨r5₃, e₃⟩ := h₃
    obtain ⟨t₄, h₄, r3₄, e₄⟩ : ∃ t₄, runBlock isa [.mov .r3 (.reg .r5)] t₃ = some t₄ ∧
        t₄.gpr .r3 = t₃.gpr .r5 ∧ Keep [.r3] t₃ t₄ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
        RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left', true_and]
      keep_tac
    refine WP.of_runBlock ⟨t₄, h₄, ?_, ?_⟩
    · rw [r3₄, r5₃]; rfl
    · exact (e₁.weaken (by decide)).trans ((e₂.weaken (by decide)).trans ((e₃.weaken (by decide)).trans
        (e₄.weaken (by decide))))

/-- Decryption subkey `n` of `z`. -/
abbrev dk (z : Spec.Idea.Schedule) (n : Nat) : Spec.Idea.Word := (Spec.Idea.invertKey z).getD n 0

/-- `r7` holds the first `i` decryption subkeys of pair `q`, and zeros above. -/
def Acc (z : Spec.Idea.Schedule) (q i : Nat) (t : State) : Prop :=
  ∀ p < 32, (t.gpr .r7).getLsbD p =
    if p < 16 * i then (dk z (2 * q + p / 16)).getLsbD (p % 16) else false

theorem invPlace_run (z : Spec.Idea.Schedule) (q i : Nat) (hi : i < 2) (t : State)
    (hr3 : t.gpr .r3 = (dk z (2 * q + i)).setWidth 32) (hacc : i = 0 ∨ Acc z q i t) :
    ∃ t', runBlock isa (invPlace (2 * q + i)) t = some t' ∧ Acc z q (i + 1) t' ∧
      Keep [.r7] t t' := by
  unfold invPlace
  split
  · rename_i h
    obtain hi0 : i = 0 := by omega_arith
    subst hi0
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun p hp => ?_, by keep_tac⟩
    rw [RegUpd.gpr_setReg_self, hr3, BitVec.getLsbD_setWidth, decide_eq_true hp, Bool.true_and,
      Nat.add_zero]
    by_cases hp16 : p < 16
    · rw [ite_eq_left (by omega_arith), Nat.div_eq_of_lt hp16, Nat.mod_eq_of_lt hp16, Nat.add_zero]
    · rw [ite_eq_right (by omega_arith)]; exact BitVec.getLsbD_of_ge _ _ (by omega_arith)
  · rename_i h
    obtain hi1 : i = 1 := by omega_arith
    subst hi1
    obtain hacc' := hacc.resolve_left (by decide)
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Nat.reduceLeDiff,
      and_self, ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun p hp => ?_, by keep_tac⟩
    rw [RegUpd.gpr_setReg_self, BitVec.getLsbD_or, hacc' p hp, hr3, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
    by_cases h1 : p < 16
    · simp [h1, show p < 16 * 2 by omega_arith]
    · simp [h1, hp, show p - 16 < 32 by omega_arith,
        show 2 * q + p / 16 = 2 * q + 1 by omega_arith, show p % 16 = p - 16 by omega_arith]

/-- The registers computing a pair of decryption subkeys writes. -/
abbrev pairWrites : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9]

theorem pairWord_ok (z : Spec.Idea.Schedule) (q i : Nat) (hq : q < 26) (hi : i < 2) (t : State)
    (hz : KeyOk z t) (hm : MaskOk t) (hacc : i = 0 ∨ Acc z q i t) {rest : Prog isa}
    {Q : State → Prop}
    (hrest : ∀ t', Acc z q (i + 1) t' → Keep pairWrites t t' → WP isa rest t' Q) :
    WP isa (.seq (invWord (2 * q + i)) (.seq (.block (invPlace (2 * q + i))) rest)) t Q := by
  apply WP.seq
  refine WP.mono (invWord_ok z (by omega_arith) t hz hm) fun t₁ h₁ => ?_
  obtain ⟨v₁, e₁⟩ := h₁
  apply WP.seq
  obtain hacc₁ : i = 0 ∨ Acc z q i t₁ := by
    rcases hacc with h | h
    · exact Or.inl h
    · right; intro p hp; rw [e₁.reg .r7 (by decide)]; exact h p hp
  obtain ⟨t₂, h₂, a₂, e₂⟩ := invPlace_run z q i hi t₁ v₁ hacc₁
  exact WP.of_runBlock ⟨t₂, h₂, hrest t₂ a₂ ((e₁.weaken (by decide)).trans (e₂.weaken (by decide)))⟩

/-- What the subkey loop needs of the state `s₁` it starts from: the
encryption subkeys (104 bytes at `r0`) readable, the decryption subkeys (104
bytes at `r1`) writable, apart, neither wrapping around, and the mask. -/
structure InvPre (s : State) : Prop where
  sched : ⟨State.addr (s.gpr .r0), 104⟩ ∈ s.rd ++ s.wr
  out : ⟨State.addr (s.gpr .r1), 104⟩ ∈ s.wr
  sep : (⟨State.addr (s.gpr .r0), 104⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 104⟩
  fit0 : (s.gpr .r0).toNat + 104 ≤ 2 ^ 32
  fit1 : (s.gpr .r1).toNat + 104 ≤ 2 ^ 32
  mask : MaskOk s

/-- After `q` pairs of decryption subkeys. -/
structure QInv (s₀ : State) (q : Nat) (t : State) : Prop where
  keep : Keep pairWrites s₀ { t with mem := s₀.mem }
  frame : Frame [⟨State.addr (s₀.gpr .r1), 4 * q⟩] s₀.mem t.mem
  words : ∀ i < q, ∀ p < 32,
    (t.mem.readW (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * i)) 32).getLsbD p =
      (dk (Spec.Idea.scheduleAt s₀.mem (State.addr (s₀.gpr .r0))) (2 * i + p / 16)).getLsbD (p % 16)

theorem QInv.keyOk {s₀ t : State} {q : Nat} (hp : InvPre s₀) (hi : QInv s₀ q t) (hq : q ≤ 26) :
    KeyOk (Spec.Idea.scheduleAt s₀.mem (State.addr (s₀.gpr .r0))) t := by
  obtain hr0 : t.gpr .r0 = s₀.gpr .r0 := hi.keep.reg .r0 (by decide)
  refine ⟨by rw [hr0, hi.keep.rd, hi.keep.wr]; exact hp.sched, by rw [hr0]; exact hp.fit0, ?_⟩
  rw [hr0]
  exact scheduleAt_congr (frame_bytes hi.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.sep.sub_right (Region.sub_prefix (by omega_arith))) (by decide))

theorem invPair_ok (s₀ : State) (hp : InvPre s₀) (q : Nat) (hq : q < 26) (t : State)
    (hi : QInv s₀ q t) : WP isa (invPair q) t (QInv s₀ (q + 1)) := by
  obtain hz := hi.keyOk hp (by omega_arith)
  obtain hm : MaskOk t := (hi.keep.reg .r12 (by decide)).trans hp.mask
  simp only [invPair, show List.range 2 = [0, 1] from rfl, List.foldr_cons, List.foldr_nil]
  refine pairWord_ok _ q 0 hq (by decide) t hz hm (Or.inl rfl) fun t₁ a₁ e₁ => ?_
  obtain m₁ : MaskOk t₁ := (e₁.reg .r12 (by decide)).trans hm
  refine pairWord_ok _ q 1 hq (by decide) t₁ (hz.keep e₁ (by decide)) m₁ (Or.inr a₁)
    fun t₂ a₂ e₂ => ?_
  obtain e := e₁.trans e₂
  obtain r1₂ : t₂.gpr .r1 = s₀.gpr .r1 := (e.reg .r1 (by decide)).trans (hi.keep.reg .r1 (by decide))
  obtain hfit : (t₂.gpr .r1).toNat + 4 * q < 2 ^ 32 := by rw [r1₂]; have := hp.fit1; omega_arith
  obtain hw : InRegions t₂.wr (State.addr (t₂.gpr .r1 + BitVec.ofNat 32 (4 * q))) 4 := by
    rw [addr_add hfit, r1₂, e.wr, hi.keep.wr]
    exact ⟨_, hp.out, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.of_runBlock ⟨({ t₂ with
      mem := t₂.mem.writeW (State.addr (t₂.gpr .r1 + BitVec.ofNat 32 (4 * q))) (t₂.gpr .r7) } : State), by rw [runBlock_cons, exec_str (by omega_arith) hw, runStep_some, runBlock_nil], ?_⟩
  rw [addr_add hfit, r1₂]
  refine ⟨⟨fun r hr => (e.reg r hr).trans (hi.keep.reg r hr), rfl, e.rd.trans hi.keep.rd,
    e.wr.trans hi.keep.wr, e.sp.trans hi.keep.sp⟩, ?_, ?_⟩
  · show Frame _ s₀.mem (t₂.mem.writeW _ _)
    rw [e.mem]
    refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega_arith)
  · intro i hiq p hp32
    show ((t₂.mem.writeW _ _).readW _ 32).getLsbD p = _
    rw [e.mem]
    by_cases he : i = q
    · subst he
      rw [Mem.readW_writeW_self32, a₂ p hp32, ite_eq_left (by omega_arith)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact hi.words i (by omega_arith) p hp32

/-- Pairs `q … q + n - 1`. -/
def pairs (q n : Nat) : Prog isa :=
  (List.range' q n).foldr (fun q rest => .seq (invPair q) rest) (.block [])

theorem pairs_ok (s₀ : State) (hp : InvPre s₀) :
    ∀ n q, q + n = 26 → ∀ t, QInv s₀ q t → WP isa (pairs q n) t (QInv s₀ 26)
  | 0, q, h, t, hi => by
    rw [Nat.add_zero] at h; subst h
    exact WP.block_nil hi
  | n + 1, q, h, t, hi => by
    simp only [pairs, List.range'_succ, List.foldr_cons]
    apply WP.seq
    exact WP.mono (invPair_ok s₀ hp q (by omega_arith) t hi) fun t₁ h₁ =>
      pairs_ok s₀ hp n (q + 1) (by omega_arith) t₁ h₁

theorem invertKey_eq : invertKey =
    .seq (.block (save .r2 invSaved ++ [setMask])) (.seq (pairs 0 26) (.block (restore .r2 invSaved))) :=
  rfl

/-- `vg_idea_invert_key` on ARMv7, with the scratch buffer (24 bytes) at `r2`. -/
def invertContract : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 104⟩
    let out : Region := ⟨State.addr (s.gpr .r1), 104⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 24⟩
    s.rd = [sched] ∧ s.wr = [out, scratch] ∧ sched.Disjoint out ∧ sched.Disjoint scratch ∧
      out.Disjoint scratch ∧
      (s.gpr .r0).toNat + 104 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 104 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 24 ≤ 2 ^ 32
  post s s' := Spec.Idea.scheduleAt s'.mem (State.addr (s.gpr .r1)) =
    Spec.Idea.invertKey (Spec.Idea.scheduleAt s.mem (State.addr (s.gpr .r0)))
  pub := PublicRegs [.r0, .r1, .r2]

theorem invert_wp (s : State) (hs : invertContract.pre s) :
    WP isa invertKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ invertContract.post s s') := by
  obtain ⟨hrd, hwr, dSO, dSS, dOS, fit0, fit1, fit2⟩ := hs
  obtain hslots : Slots 0 24 invSaved := by decide
  obtain hinS : ∀ d, 0 ≤ d → d + 4 ≤ 24 → InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 d) 4 :=
    fun d _ h => ⟨⟨State.addr (s.gpr .r2), 24⟩, by rw [hwr]; simp, Offset.contains_base _ h (by omega_arith)⟩
  rw [invertKey_eq]
  refine WP.seq (save_slots_ok hslots fit2 hinS ?_)
  obtain hf₁ : Frame [⟨State.addr (s.gpr .r2), 24⟩] s.mem
      (saveMem s.mem (State.addr (s.gpr .r2)) s.gpr invSaved) :=
    saveMem_frame _ _ _ (by decide) _ (by decide)
  obtain hsv₁ := saveMem_saved (State.addr (s.gpr .r2)) s.gpr s.mem invSaved hslots
  generalize saveMem s.mem (State.addr (s.gpr .r2)) s.gpr invSaved = M₁ at hf₁ hsv₁
  let s₁ : State := { s with mem := M₁ }
  obtain ⟨s₂, h₂, m₂, e₂⟩ := setMask_run s₁
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain g₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s.gpr r := fun r hr => e₂.reg r (by simpa using hr)
  have mem₂ : s₂.mem = M₁ := e₂.mem
  obtain hp : InvPre s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, m₂⟩
    · rw [g₂ _ (by decide), e₂.rd, e₂.wr]; show _ ∈ s.rd ++ s.wr; rw [hrd]; simp
    · rw [g₂ _ (by decide), e₂.wr]; show _ ∈ s.wr; rw [hwr]; simp
    · rw [g₂ _ (by decide), g₂ _ (by decide)]; exact dSO
    · rw [g₂ _ (by decide)]; exact fit0
    · rw [g₂ _ (by decide)]; exact fit1
  obtain sched₂ : Spec.Idea.scheduleAt s₂.mem (State.addr (s₂.gpr .r0)) =
      Spec.Idea.scheduleAt s.mem (State.addr (s.gpr .r0)) := by
    rw [mem₂, g₂ _ (by decide)]
    exact scheduleAt_congr (frame_bytes hf₁ (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact dSS) (by decide))
  refine WP.seq (WP.mono (pairs_ok s₂ hp 26 0 rfl s₂ ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩,
    Frame.refl _ _, fun i hi => absurd hi (by omega_arith)⟩) fun t ht => ?_)
  -- Restoring the registers.
  obtain r2t : t.gpr .r2 = s.gpr .r2 := (ht.keep.reg .r2 (by decide)).trans (g₂ _ (by decide))
  obtain hsv : Saved t.mem (State.addr (t.gpr .r2)) s.gpr invSaved := by
    rw [r2t]
    refine hsv₁.frame hslots (mem₂ ▸ ht.frame) fun q hq => ?_
    simp only [List.mem_singleton] at hq; subst hq
    rw [BitVec.add_zero, g₂ _ (by decide)]
    exact dOS.symm.sub_right (Region.sub_prefix (by omega_arith))
  obtain hin : ∀ d, 0 ≤ d → d + 4 ≤ 24 →
      InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r2) + BitVec.ofNat 64 d) 4 := fun d h0 h => by
    obtain ⟨R, hR, hc⟩ := hinS d h0 h
    rw [ht.keep.rd, ht.keep.wr, e₂.rd, e₂.wr, r2t]
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  refine WP.mono (restore_block_ok hslots (by decide) (by rw [r2t]; exact fit2) hin hsv)
    fun u hu' => ?_
  obtain ⟨hu, ho, hm, -⟩ := hu'
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hu (.r4, 0) (by decide)
    · exact hu (.r5, 4) (by decide)
    · exact hu (.r6, 8) (by decide)
    · exact hu (.r7, 12) (by decide)
    · exact hu (.r8, 16) (by decide)
    · exact hu (.r9, 20) (by decide)
    all_goals rw [ho _ (by decide), ht.keep.reg _ (by decide), g₂ _ (by decide)]
  · show Spec.Idea.scheduleAt u.mem _ = _
    rw [hm, ← g₂ .r1 (by decide), ← sched₂]
    apply Vector.ext
    intro n hn
    rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    rw [scheduleAt_getLsbD32 _ _ hn hb, ht.words (n / 2) (by omega_arith) _ (by omega_arith),
      show 2 * (n / 2) + (16 * (n % 2) + b) / 16 = n by omega_arith,
      show (16 * (n % 2) + b) % 16 = b by omega_arith]

theorem invert_correct (s : State) (hs : invertContract.pre s) :
    ∃ t s', Exec isa invertKey s t s' ∧ abiPreserved s s' ∧ invertContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := invert_wp s hs
  exact ⟨t, s', he, ⟨ha, Exec.sp he⟩, hp⟩

def invertSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 104⟩, ⟨0x3000, 24⟩]

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.r0, .r1, .r2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 := by
  simp [PublicRegs]

theorem invertKey_verified : Verified target invertKey (Proof.Idea.invertKeyScratchContract32 abi 6) := by
  refine Verified.of_correct invert_correct (invertKey_constantTime _) ?_
  sig_implies [Proof.Idea.invertKeyScratchContract32, Proof.Idea.invertKeyScratchSig32,
    Spec.Idea.invertKeyPost, abi, argRegs, reduceClassify, Loc.val, State.addr, invertContract,
    publicRegs_three] [invertSat] using invertSat

end VG.Proof.Idea.Arm

end

end


/-!
# Verified IDEA on ARMv7, with its saved registers on the stack

`vg_idea_ecb` and `vg_idea_invert_key` save the callee-saved registers they
use in a buffer passed in a register (`r3`, `r2`), proved with the buffer as
an argument (`Ecb.lean`, `Invert.lean`); `ecb_framed` and `invertKey_framed`
allocate it in a frame of their own (`Verified.regScratch`). The buffer only
ever holds the caller's registers, so it is not zeroed.
-/

@[expose] public section

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Impl.Idea.Arm

/-- A state satisfying the ECB precondition without the buffer. -/
def ecbFrameSat : State := { satState with wr := [⟨0x2000, 8⟩] }

theorem ecbFrameSat_pre : ∃ s, (Spec.Idea.ecbContract Arm.abi 32).pre s := by
  implies_sat [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Spec.Idea.ecbPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [ecbFrameSat, satState] using ecbFrameSat

theorem ecb_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 32 .r3 ecb)
    (Spec.Idea.ecbContract Arm.abi 32) :=
  Arm.Verified.regScratch (sig := Spec.Idea.ecbSig) (nm := "scratch") (e := .u32) (n := 8)
    (post := Spec.Idea.ecbPost Arm.abi.ptrBits) (wa := false) (stack := 0) ecb_verified
    (by decide) (by decide) (by decide)
    (fun vs mm m₁ m₂ r hl _ => Proof.Idea.ecbPostOut_local _ vs mm m₁ m₂ r hl) ecbFrameSat_pre

/-- A state satisfying the inversion's precondition without the buffer. -/
def invertFrameSat : State := { invertSat with wr := [⟨0x2000, 104⟩] }

theorem invertFrameSat_pre : ∃ s, (Spec.Idea.invertKeyContract Arm.abi 24).pre s := by
  implies_sat [Spec.Idea.invertKeyContract, Spec.Idea.invertKeySig, Spec.Idea.invertKeyPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [invertFrameSat, invertSat]
    using invertFrameSat

theorem invertKey_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 24 .r2 invertKey)
    (Spec.Idea.invertKeyContract Arm.abi 24) :=
  Arm.Verified.regScratch (sig := Spec.Idea.invertKeySig) (nm := "scratch") (e := .u32) (n := 6)
    (post := Spec.Idea.invertKeyPost Arm.abi.ptrBits) (wa := false) (stack := 0) invertKey_verified
    (by decide) (by decide) (by decide)
    (fun vs mm m₁ m₂ r hl _ => Proof.Idea.invertKeyPostOut_local _ vs mm m₁ m₂ r hl) invertFrameSat_pre

end VG.Proof.Idea.Arm
