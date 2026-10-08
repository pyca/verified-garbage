import VerifiedGarbage.Proof.Idea.X86_64.Mul

/-!
# IDEA on x86-64: a round

`round_run`: round `j` of the code (`Impl.Idea.X86_64.round j`) maps the
state words in `r8`–`r11` (`Holds`) to `Spec.Idea.round` of them under
subkeys `6j … 6j + 5`, read from the schedule at `rdi` (`KeyOk`). It is
composed of runs of its pieces: ⊙ and ⊞ with a subkey (`mulKey_run`,
`addKey_run`), and the multiplication–addition structure.
-/

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64

/-- The state words are in `r8`–`r11`, zero-extended. -/
structure Holds (x : Spec.Idea.State) (s : State) : Prop where
  r8 : s.gpr .r8 = (x.getD 0 0).setWidth 64
  r9 : s.gpr .r9 = (x.getD 1 0).setWidth 64
  r10 : s.gpr .r10 = (x.getD 2 0).setWidth 64
  r11 : s.gpr .r11 = (x.getD 3 0).setWidth 64

/-- Subkey `k` of `z`, at `rdi + 2k` (`k ≤ 48`), can be loaded: a quadword
whose low 16 bits it is; and subkeys `48 + j` are the words of the quadword
at `rdi + 96`. -/
structure KeyOk (z : Spec.Idea.Schedule) (s : State) : Prop where
  low : ∀ k ≤ 48, InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi (2 * k))) 8 ∧
    (s.mem.readW (s.ea (at_ .rdi (2 * k))) 64).setWidth 16 = z.getD k 0
  last : ∀ j < 4, ((s.mem.readW (s.ea (at_ .rdi 96)) 64) >>> (16 * j)).setWidth 16 = z.getD (48 + j) 0

theorem KeyOk.keep {z : Spec.Idea.Schedule} {rs : List Reg} {s s' : State} (h : KeyOk z s)
    (hk : Keep rs s s') (hrdi : .rdi ∉ rs) : KeyOk z s' := by
  have he : ∀ d, s'.ea (at_ .rdi d) = s.ea (at_ .rdi d) := fun d => by
    simp only [State.ea, at_, hk.reg .rdi hrdi]
  refine ⟨fun k hk' => ?_, fun j hj => ?_⟩
  · rw [he, hk.rd, hk.wr, hk.mem]
    exact h.low k hk'
  · rw [he, hk.mem]
    exact h.last j hj

theorem setWidth_setWidth16 (x : BitVec 16) : (x.setWidth 64).setWidth 16 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- `add r, y; and r, 0xffff` on a zero-extended word. -/
theorem add_mask (x : BitVec 16) (y : BitVec 64) :
    (x.setWidth 64 + y) &&& 65535 = (x + y.setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [mask_toNat _ _ rfl]
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

theorem add_setWidth (x y : BitVec 16) :
    (x.setWidth 64 + y.setWidth 64).setWidth 16 = x + y := by
  rw [BitVec.setWidth_add _ _ (by decide), setWidth_setWidth16, setWidth_setWidth16]

theorem xor_setWidth (x y : BitVec 16) : x.setWidth 64 ^^^ y.setWidth 64 = (x ^^^ y).setWidth 64 := by
  rw [BitVec.setWidth_xor]

macro "run_simp" : tactic => `(tactic| simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
  execAlu, execShift, readSrc, State.load64, isa, Option.map_some, Option.bind_some,
  signExtend_one, signExtend_mask])

/-- `r := r ⊙ [rdi + d]`. -/
theorem mulKey_run (r : Reg) (d : Nat) (s : State)
    (hk : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi d)) 8) :
    ∃ s', runBlock isa (mulKey r d) s = some s' ∧
      s'.gpr r = (Spec.Idea.mul ((s.gpr r).setWidth 16)
        ((s.mem.readW (s.ea (at_ .rdi d)) 64).setWidth 16)).setWidth 64 ∧
      Keep [.rax, .rdx, r] s s' := by
  have h₁ : runBlock isa [.mov .rax (.reg r), .mov .rdx (.mem (at_ .rdi d))] s =
      some ((s.setReg .rax (s.gpr r)).setReg .rdx (s.mem.readW (s.ea (at_ .rdi d)) 64)) := by
    simp only [runBlock_cons, runStep_some, exec, readSrc, State.load64, isa,
      Option.map_some, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.ea, at_,
      RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]
    simp only [State.ea, at_] at hk
    simp only [hk, ↓reduceIte, Option.map_some, runStep_some, runBlock_nil]
  obtain ⟨s₂, h₂, v₂, k₂⟩ := mul_run ((s.setReg .rax (s.gpr r)).setReg .rdx
    (s.mem.readW (s.ea (at_ .rdi d)) 64))
  have h₃ : runBlock isa [.mov r (.reg .rdx)] s₂ = some (s₂.setReg r (s₂.gpr .rdx)) := by
    run_simp
  refine ⟨_, run_append (run_append h₁ h₂) h₃, ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg_self, v₂, RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]
  · refine ⟨fun q hq => ?_, k₂.mem, k₂.rd, k₂.wr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [RegUpd.gpr_setReg_of_ne _ _ hq.2.2, k₂.reg q (by simp [hq.1, hq.2.1]),
      RegUpd.gpr_setReg_of_ne _ _ hq.2.1, RegUpd.gpr_setReg_of_ne _ _ hq.1]

/-- `r := r ⊞ [rdi + d]`, zero-extended. -/
theorem addKey_run {r : Reg} (hrd : r ≠ .rdx) (d : Nat) (s : State) (x : BitVec 16)
    (hx : s.gpr r = x.setWidth 64)
    (hk : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi d)) 8) :
    ∃ s', runBlock isa (addKey r d) s = some s' ∧
      s'.gpr r = (x + (s.mem.readW (s.ea (at_ .rdi d)) 64).setWidth 16).setWidth 64 ∧
      Keep [.rdx, r] s s' := by
  simp only [State.ea, at_] at hk
  simp only [addKey, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64,
    isa, Option.map_some, Option.bind_some, signExtend_mask, State.ea, at_, hk, ↓reduceIte,
    RegUpd.gpr_setReg, hrd, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hq => ?_, rfl, rfl, rfl⟩
  · rw [hx]; exact add_mask x _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq.1, hq.2, ite_false]

/-- The registers but `written` keep their values (for `Keep` of explicit states). -/
theorem keep_reg_of {written : List Reg} {s s' : State}
    (h : ∀ r, r ∉ written → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Keep written s s' := ⟨h, hm, hrd, hwr⟩

theorem p5_run (s : State) (d : Nat) (hk : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi d)) 8) :
    ∃ s', runBlock isa [.mov .rax (.reg .r8), .alu .xor .rax (.reg .r10),
        .mov .rdx (.mem (at_ .rdi d))] s = some s' ∧
      s'.gpr .rax = s.gpr .r8 ^^^ s.gpr .r10 ∧ s'.gpr .rdx = s.mem.readW (s.ea (at_ .rdi d)) 64 ∧
      Keep [.rax, .rdx] s s' := by
  simp only [State.ea, at_] at hk ⊢
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64,
    isa, Option.map_some, Option.bind_some, State.ea, hk, ↓reduceIte,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, Option.some.injEq, exists_eq_left',
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, true_and]
  refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq.1, hq.2, ite_false]

theorem p6_run (s : State) (d : Nat) (hk : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi d)) 8) :
    ∃ s', runBlock isa [.mov .rbx (.reg .rdx), .mov .rax (.reg .r9), .alu .xor .rax (.reg .r11),
        .alu .add .rax (.reg .rbx), .mov .rdx (.mem (at_ .rdi d))] s = some s' ∧
      s'.gpr .rbx = s.gpr .rdx ∧ s'.gpr .rax = (s.gpr .r9 ^^^ s.gpr .r11) + s.gpr .rdx ∧
      s'.gpr .rdx = s.mem.readW (s.ea (at_ .rdi d)) 64 ∧ Keep [.rax, .rbx, .rdx] s s' := by
  simp only [State.ea, at_] at hk ⊢
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64,
    isa, Option.map_some, Option.bind_some, State.ea, hk, ↓reduceIte,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, Option.some.injEq, exists_eq_left',
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, true_and]
  refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq.1, hq.2.1, hq.2.2, ite_false]

theorem p7_run (s : State) :
    ∃ s', runBlock isa [.alu .add .rbx (.reg .rdx), .alu .and .rbx (.imm 0xffff),
        .alu .xor .r8 (.reg .rdx), .alu .xor .r10 (.reg .rdx),
        .alu .xor .r9 (.reg .rbx), .alu .xor .r11 (.reg .rbx),
        .mov .rax (.reg .r9), .mov .r9 (.reg .r10), .mov .r10 (.reg .rax)] s = some s' ∧
      s'.gpr .r8 = s.gpr .r8 ^^^ s.gpr .rdx ∧
      s'.gpr .r9 = s.gpr .r10 ^^^ s.gpr .rdx ∧
      s'.gpr .r10 = s.gpr .r9 ^^^ ((s.gpr .rbx + s.gpr .rdx) &&& 65535) ∧
      s'.gpr .r11 = s.gpr .r11 ^^^ ((s.gpr .rbx + s.gpr .rdx) &&& 65535) ∧
      Keep [.rax, .rbx, .r8, .r9, .r10, .r11] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    isa, Option.map_some, Option.bind_some, ↓reduceIte, signExtend_mask,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, Option.some.injEq, exists_eq_left',
    true_and]
  refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1,
    hq.2.2.2.2.1, hq.2.2.2.2.2, ite_false]

/-- The written registers of a round. -/
abbrev roundWrites : List Reg := [.rax, .rdx, .rbx, .r8, .r9, .r10, .r11]

theorem Keep.weaken {rs : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : (rs.all fun r => roundWrites.contains r) = true) : Keep roundWrites s s' :=
  h.mono fun r hr => by
    have := List.all_eq_true.mp hs r hr
    simpa using this

/-- Subkey `6j + i` of a round, at its offset. -/
theorem key_at {z : Spec.Idea.Schedule} {s : State} (hk : KeyOk z s) (j i : Nat) (h : 6 * j + i ≤ 48) :
    InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi (12 * j + 2 * i))) 8 ∧
      (s.mem.readW (s.ea (at_ .rdi (12 * j + 2 * i))) 64).setWidth 16 = z.getD (6 * j + i) 0 := by
  have := hk.low (6 * j + i) h
  rwa [show 2 * (6 * j + i) = 12 * j + 2 * i by omega] at this

theorem round_run (j : Nat) (hj : j < 8) (z : Spec.Idea.Schedule) (x : Spec.Idea.State)
    (s : State) (hx : Holds x s) (hk : KeyOk z s) :
    ∃ s', runBlock isa (round j) s = some s' ∧
      Holds (Spec.Idea.round (z.getD (6 * j) 0) (z.getD (6 * j + 1) 0) (z.getD (6 * j + 2) 0)
        (z.getD (6 * j + 3) 0) (z.getD (6 * j + 4) 0) (z.getD (6 * j + 5) 0) x) s' ∧
      Keep roundWrites s s' := by
  have k0 := key_at hk j 0 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at k0
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mulKey_run .r8 (12 * j) s k0.1
  rw [hx.r8, setWidth_setWidth16, k0.2] at v₁
  have hk₁ := hk.keep e₁ (by decide)
  have k3 := key_at hk₁ j 3 (by omega)
  simp only [Nat.reduceMul] at k3
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mulKey_run .r11 (12 * j + 6) s₁ k3.1
  rw [e₁.reg .r11 (by decide), hx.r11, setWidth_setWidth16, k3.2] at v₂
  have hk₂ := hk₁.keep e₂ (by decide)
  have k1 := key_at hk₂ j 1 (by omega)
  simp only [Nat.mul_one] at k1
  obtain ⟨s₃, h₃, v₃, e₃⟩ := addKey_run (r := .r9) (by decide) (12 * j + 2) s₂ (x.getD 1 0)
    ((e₂.reg .r9 (by decide)).trans ((e₁.reg .r9 (by decide)).trans hx.r9)) k1.1
  rw [k1.2] at v₃
  have hk₃ := hk₂.keep e₃ (by decide)
  have k2 := key_at hk₃ j 2 (by omega)
  simp only [Nat.reduceMul] at k2
  obtain ⟨s₄, h₄, v₄, e₄⟩ := addKey_run (r := .r10) (by decide) (12 * j + 4) s₃ (x.getD 2 0)
    ((e₃.reg .r10 (by decide)).trans ((e₂.reg .r10 (by decide)).trans
      ((e₁.reg .r10 (by decide)).trans hx.r10))) k2.1
  rw [k2.2] at v₄
  have hk₄ := hk₃.keep e₄ (by decide)
  have k4 := key_at hk₄ j 4 (by omega)
  simp only [Nat.reduceMul] at k4
  obtain ⟨s₅, h₅, a₅, d₅, e₅⟩ := p5_run s₄ (12 * j + 8) k4.1
  obtain ⟨s₆, h₆, v₆, e₆⟩ := mul_run s₅
  have hk₆ := (hk₄.keep e₅ (by decide)).keep e₆ (by decide)
  have k5 := key_at hk₆ j 5 (by omega)
  simp only [Nat.reduceMul] at k5
  obtain ⟨s₇, h₇, b₇, a₇, d₇, e₇⟩ := p6_run s₆ (12 * j + 10) k5.1
  obtain ⟨s₈, h₈, v₈, e₈⟩ := mul_run s₇
  obtain ⟨s₉, h₉, r8₉, r9₉, r10₉, r11₉, e₉⟩ := p7_run s₈
  refine ⟨s₉, ?_, ?_, ?_⟩
  · simp only [round]
    exact run_append (run_append (run_append (run_append (run_append (run_append (run_append
      (run_append h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉
  · -- The words through the pieces.
    have m₄ : s₄.mem = s.mem := e₄.mem.trans (e₃.mem.trans (e₂.mem.trans e₁.mem))
    have r8₄ : s₄.gpr .r8 = (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0)).setWidth 64 :=
      (e₄.reg .r8 (by decide)).trans ((e₃.reg .r8 (by decide)).trans ((e₂.reg .r8 (by decide)).trans v₁))
    have r11₄ : s₄.gpr .r11 = (Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)).setWidth 64 :=
      (e₄.reg .r11 (by decide)).trans ((e₃.reg .r11 (by decide)).trans v₂)
    have r9₄ : s₄.gpr .r9 = (x.getD 1 0 + z.getD (6 * j + 1) 0).setWidth 64 :=
      (e₄.reg .r9 (by decide)).trans v₃
    have t₀ : s₆.gpr .rdx = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
        (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0)).setWidth 64 := by
      rw [v₆, a₅, d₅, r8₄, v₄, xor_setWidth, setWidth_setWidth16, k4.2]
    have keep₆ : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s₆.gpr r = s₄.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact (e₆.reg _ (by decide)).trans (e₅.reg _ (by decide))
    have t₁ : s₈.gpr .rdx = (Spec.Idea.mul (((x.getD 1 0 + z.getD (6 * j + 1) 0) ^^^
        Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
          (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0))
        (z.getD (6 * j + 5) 0)).setWidth 64 := by
      rw [v₈, a₇, d₇, keep₆ .r9 (by simp), keep₆ .r11 (by simp), r9₄, r11₄, t₀, xor_setWidth,
        add_setWidth, k5.2]
    have keep₈ : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s₈.gpr r = s₄.gpr r := by
      intro r hr
      have h := keep₆ r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact (e₈.reg _ (by decide)).trans ((e₇.reg _ (by decide)).trans h)
    have rbx₈ : s₈.gpr .rbx = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
        (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0)).setWidth 64 := by
      rw [e₈.reg .rbx (by decide), b₇, t₀]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [r8₉, keep₈ .r8 (by simp), r8₄, t₁, xor_setWidth]; rfl
    · rw [r9₉, keep₈ .r10 (by simp), v₄, t₁, xor_setWidth]; rfl
    · rw [r10₉, keep₈ .r9 (by simp), r9₄, rbx₈, t₁, add_mask, setWidth_setWidth16, xor_setWidth]; rfl
    · rw [r11₉, keep₈ .r11 (by simp), r11₄, rbx₈, t₁, add_mask, setWidth_setWidth16, xor_setWidth]; rfl
  · exact (e₁.weaken (by decide)).trans ((e₂.weaken (by decide)).trans ((e₃.weaken (by decide)).trans
      ((e₄.weaken (by decide)).trans ((e₅.weaken (by decide)).trans ((e₆.weaken (by decide)).trans
      ((e₇.weaken (by decide)).trans ((e₈.weaken (by decide)).trans (e₉.weaken (by decide)))))))))

end VG.Proof.Idea.X86_64
