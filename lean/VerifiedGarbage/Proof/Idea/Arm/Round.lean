import VerifiedGarbage.Proof.Idea.Arm.Mul
import VerifiedGarbage.Proof.Idea.Memory32

/-!
# IDEA on ARMv7: a round

`round_run`: round `j` of the code (`roundWith j b c`) maps the state words
in `r4`, `b`, `c`, `r7` (`Holds`) to `Spec.Idea.round` of them under subkeys
`6j … 6j + 5`, each loaded from the schedule at `r0` (`KeyOk`) when it is
used, and leaves the new middle words in `c` and `b`.
-/

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
  have hfit : (s.gpr .r0).toNat + off < 2 ^ 32 := by have := hk.fit; omega
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 off)) 4 := by
    rw [addr_add hfit]
    exact ⟨_, hk.read, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨_, by rw [runBlock_cons, exec_ldr (by omega) hin, runStep_some, runBlock_nil], ?_, ?_⟩
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
    obtain ⟨s₁, h₁, v₁, e₁⟩ := ldr_key_run r (2 * k) (by omega) s hk
    exact ⟨s₁, h₁, by rw [v₁, subkey_lo32 _ _ (by omega), hk.sched], e₁⟩

/-- A data-processing instruction with a register operand. -/
theorem dp_run (op : DpOp) (d n r : Reg) (s : State) :
    ∃ s', runBlock isa [.dp op d n (.reg r)] s = some s' ∧
      s'.gpr d = (match op with
        | .add => s.gpr n + s.gpr r | .sub => s.gpr n - s.gpr r | .and => s.gpr n &&& s.gpr r
        | .orr => s.gpr n ||| s.gpr r | .eor => s.gpr n ^^^ s.gpr r) ∧
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
  have nb : ∀ r ∈ [Reg.r0, .r4, .r7, .r8, .r9, .r10, .r11, .r12], b ≠ r ∧ c ≠ r := by
    intro r hr
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hbc : b ≠ c := by
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide
  have hsub : ∀ r ∈ [b, c], r ∈ roundWrites := by
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
  have kb : ∀ {rs : List Reg} {s s' : State}, Keep rs s s' →
      (∀ r ∈ rs, r ∈ [Reg.r4, .r7, .r8, .r9, .r10, .r11]) → s'.gpr b = s.gpr b ∧ s'.gpr c = s.gpr c :=
    fun {rs s s'} e h => ⟨e.reg b fun hm => by
        rcases List.mem_cons.mp (h b hm) with h' | h' <;> simp_all,
      e.reg c fun hm => by rcases List.mem_cons.mp (h c hm) with h' | h' <;> simp_all⟩
  have r12 : ∀ {rs : List Reg} {s s' : State}, Keep rs s s' → .r12 ∉ rs → MaskOk s → MaskOk s' :=
    fun e h hm => (e.reg .r12 h).trans hm
  -- X₁ ⊙ Z₁
  obtain ⟨s₁, h₁, v₁, e₁⟩ := loadKey_run .r9 (6 * j) (by omega) s hk
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mul_run .r4 .r4 .r9 (by decide) s₁ (r12 e₁ (by decide) hm)
  -- X₄ ⊙ Z₄
  obtain ⟨s₃, h₃, v₃, e₃⟩ := loadKey_run .r9 (6 * j + 3) (by omega) s₂
    ((hk.keep e₁ (by decide)).keep e₂ (by decide))
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mul_run .r7 .r7 .r9 (by decide) s₃
    (r12 e₃ (by decide) (r12 e₂ (by decide) (r12 e₁ (by decide) hm)))
  have e₀₄ : Keep [.r4, .r7, .r8, .r9] s s₄ :=
    (((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))).trans
      (e₄.weaken (by decide))
  have k₄ : KeyOk z s₄ := hk.keep e₀₄ (by decide)
  have m₄ : MaskOk s₄ := r12 e₀₄ (by decide) hm
  -- X₂ ⊞ Z₂, X₃ ⊞ Z₃
  obtain ⟨s₅, h₅, v₅, e₅⟩ := loadKey_run .r9 (6 * j + 1) (by omega) s₄ k₄
  obtain ⟨s₆, h₆, v₆, e₆⟩ := addKey_run b b12 s₅ (r12 e₅ (by decide) m₄)
  obtain ⟨s₇, h₇, v₇, e₇⟩ := loadKey_run .r9 (6 * j + 2) (by omega) s₆
    ((k₄.keep e₅ (by decide)).keep e₆ (by simpa using b0.symm))
  obtain ⟨s₈, h₈, v₈, e₈⟩ := addKey_run c c12 s₇
    (r12 e₇ (by decide) (r12 e₆ (by simpa using b12.symm) (r12 e₅ (by decide) m₄)))
  have e₄₈ : Keep [.r9, b, c] s₄ s₈ :=
    (((e₅.mono (by simp)).trans (e₆.mono (by simp))).trans (e₇.mono (by simp))).trans
      (e₈.mono (by simp))
  have k₈ : KeyOk z s₈ := k₄.keep e₄₈ (by simp [b0.symm, c0.symm])
  have m₈ : MaskOk s₈ := r12 e₄₈ (by simp [b12.symm, c12.symm]) m₄
  -- t₀
  obtain ⟨s₉, h₉, v₉, e₉⟩ := dp_run .eor .r10 .r4 c s₈
  obtain ⟨s₁₀, h₁₀, v₁₀, e₁₀⟩ := loadKey_run .r9 (6 * j + 4) (by omega) s₉ (k₈.keep e₉ (by decide))
  obtain ⟨s₁₁, h₁₁, v₁₁, e₁₁⟩ := mul_run .r10 .r10 .r9 (by decide) s₁₀
    (r12 e₁₀ (by decide) (r12 e₉ (by decide) m₈))
  -- t₁
  obtain ⟨s₁₂, h₁₂, v₁₂, e₁₂⟩ := dp_run .eor .r11 b .r7 s₁₁
  obtain ⟨s₁₃, h₁₃, v₁₃, e₁₃⟩ := dp_run .add .r11 .r11 .r10 s₁₂
  have e₈₁₃ : Keep [.r8, .r9, .r10, .r11] s₈ s₁₃ :=
    ((((e₉.weaken (by decide)).trans (e₁₀.weaken (by decide))).trans (e₁₁.weaken (by decide))).trans
      (e₁₂.weaken (by decide))).trans (e₁₃.weaken (by decide))
  obtain ⟨s₁₄, h₁₄, v₁₄, e₁₄⟩ := loadKey_run .r9 (6 * j + 5) (by omega) s₁₃ (k₈.keep e₈₁₃ (by decide))
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
    have t : runBlock isa ([.dp .add .r10 .r10 (.reg .r11), .dp .and .r10 .r10 (.reg .r12),
        .dp .eor .r4 .r4 (.reg .r11), .dp .eor c c (.reg .r11),
        .dp .eor b b (.reg .r10), .dp .eor .r7 .r7 (.reg .r10)] : List Instr) s₁₅ = some s₂₁ :=
      run_append h₁₆ (run_append h₁₇ (run_append h₁₈ (run_append h₁₉ (run_append h₂₀ h₂₁))))
    have m : runBlock isa ([.dp .eor .r11 b (.reg .r7), .dp .add .r11 .r11 (.reg .r10)] : List Instr) s₁₁ =
        some s₁₃ := run_append h₁₂ h₁₃
    exact run_append (run_append (run_append (run_append (run_append (run_append (run_append
      (run_append (run_append (run_append (run_append (run_append (run_append (run_append
      h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉) h₁₀) h₁₁) m) h₁₄) h₁₅) t
  · -- The values, from the last write back.
    have a : s₈.gpr .r4 = (Spec.Idea.mul (x.getD 0 0) (rk z j 0)).setWidth 32 := by
      rw [e₄₈.reg .r4 (by simp [b4.symm, c4.symm]), e₄.reg .r4 (by decide), e₃.reg .r4 (by decide), v₂,
        e₁.reg .r4 (by decide), hx.r4, setWidth_setWidth16_32, v₁]
      rfl
    have d : s₈.gpr .r7 = (Spec.Idea.mul (x.getD 3 0) (rk z j 3)).setWidth 32 := by
      rw [e₄₈.reg .r7 (by simp [b7.symm, c7.symm]), v₄, v₃, e₃.reg .r7 (by decide),
        e₂.reg .r7 (by decide), e₁.reg .r7 (by decide), hx.r7, setWidth_setWidth16_32]
    have bv : s₈.gpr b = (x.getD 1 0 + rk z j 1).setWidth 32 := by
      have hb₄ := (kb e₀₄ (by decide)).1
      rw [e₈.reg b (by simpa using hbc), e₇.reg b (by simpa using b9), v₆, e₅.reg b (by simpa using b9),
        hb₄, hx.b, add_mask32, v₅]
    have cv : s₈.gpr c = (x.getD 2 0 + rk z j 2).setWidth 32 := by
      have hc₄ := (kb e₀₄ (by decide)).2
      rw [v₈, e₇.reg c (by simpa using c9), e₆.reg c (by simpa using Ne.symm hbc),
        e₅.reg c (by simpa using c9), hc₄, hx.c, add_mask32, v₇]
    have t₀ : s₁₁.gpr .r10 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^
        (x.getD 2 0 + rk z j 2)) (rk z j 4)).setWidth 32 := by
      rw [v₁₁, e₁₀.reg .r10 (by decide), v₉, a, cv, xor_setWidth32, setWidth_setWidth16_32, v₁₀]
    have keep₁₅ : ∀ r ∈ [Reg.r4, .r7], s₁₅.gpr r = s₈.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact (e₁₅.reg _ (by decide)).trans ((e₁₄.reg _ (by decide)).trans (e₈₁₃.reg _ (by decide)))
    have kbc₁₅ := kb ((e₈₁₃.trans (e₁₄.weaken (by decide))).trans (e₁₅.weaken (by decide))) (by decide)
    have t₁ : s₁₅.gpr .r11 = (Spec.Idea.mul (((x.getD 1 0 + rk z j 1) ^^^
        Spec.Idea.mul (x.getD 3 0) (rk z j 3)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^ (x.getD 2 0 + rk z j 2)) (rk z j 4))
        (rk z j 5)).setWidth 32 := by
      rw [v₁₅, e₁₄.reg .r11 (by decide), v₁₃, v₁₂, e₁₂.reg .r10 (by decide), t₀,
        e₁₁.reg b (by simp [b8, b9, b10]), e₁₀.reg b (by simpa using b9),
        e₉.reg b (by simpa using b10), bv,
        e₁₁.reg .r7 (by decide), e₁₀.reg .r7 (by decide), e₉.reg .r7 (by decide), d,
        xor_setWidth32, add_setWidth32, v₁₄]
    have kbc₁₇ := kb ((e₁₆.weaken (rs' := [.r10]) (by decide)).trans (e₁₇.weaken (by decide))) (by decide)
    have r10₁₅ : s₁₅.gpr .r10 = s₁₁.gpr .r10 := by
      rw [e₁₅.reg .r10 (by decide), e₁₄.reg .r10 (by decide), e₁₃.reg .r10 (by decide)]
      · exact e₁₂.reg .r10 (by decide)
    have r10₁₇ : s₁₇.gpr .r10 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^
        (x.getD 2 0 + rk z j 2)) (rk z j 4) + Spec.Idea.mul (((x.getD 1 0 + rk z j 1) ^^^
        Spec.Idea.mul (x.getD 3 0) (rk z j 3)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^ (x.getD 2 0 + rk z j 2)) (rk z j 4))
        (rk z j 5)).setWidth 32 := by
      rw [v₁₇, v₁₆, e₁₆.reg .r12 (by decide), e₁₅.reg .r12 (by decide), e₁₄.reg .r12 (by decide),
        e₈₁₃.reg .r12 (by decide), m₈, r10₁₅, t₀, t₁, add_mask32, setWidth_setWidth16_32]
    have r11₁₇ : s₁₇.gpr .r11 = s₁₅.gpr .r11 := by
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
    have hC : ∀ r ∈ [c], r ∈ roundWrites := fun r hr => hsub r (by simp at hr; simp [hr])
    have e₄₈' : Keep roundWrites s₄ s₈ := e₄₈.mono fun r hr => by
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
