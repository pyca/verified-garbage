module

public import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.Idea.X86_64
public import VerifiedGarbage.Spec.Idea
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! ### `Idea.X86_64.Round`, which this module and modules that import it used -/

section

/-! ### `Idea.X86_64.Mul`, which only this module used -/

section

/-!
# IDEA on x86-64: ⊙ without branches

`mul_run`: `mulCode` leaves `rax ⊙ rdx` (of their low 16 bits) in `rdx`,
and changes nothing but `rax`, `rdx` and the flags. The arithmetic is
`prep_toNat` (the operands' residues) and `reduce` (the product modulo
2¹⁶ + 1 from its halves, corrected by the sign of their difference).
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64

/-- What a block keeps: every register but `written`, memory and regions. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r fun hm => hr (hs r hm), h.mem, h.rd, h.wr⟩

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil, Option.bind_some]
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- Composing two runs. -/
theorem run_append {a b : List Instr} {s s₁ s₂ : State}
    (h₁ : runBlock isa a s = some s₁) (h₂ : runBlock isa b s₁ = some s₂) :
    runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_append, h₁, Option.bind_some, h₂]

theorem signExtend_one : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem signExtend_mask : BitVec.signExtend 64 (65535 : BitVec 32) = 65535 := by decide

/-- The low product is shared by signed and unsigned multiplication. -/
theorem lowProduct (a b : BitVec 64) :
    a * b = BitVec.ofNat 64 (a.toNat * b.toNat) := by
  simp only [BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `mulCode` on the machine. -/
theorem mul_run (s : State) : ∃ s', runBlock isa mulCode s = some s' ∧
    s'.gpr .rdx = (Spec.Idea.mul ((s.gpr .rax).setWidth 16) ((s.gpr .rdx).setWidth 16)).setWidth 64 ∧
    Keep [.rax, .rdx] s s' := by
  simp only [mulCode, runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu, execShift, execImul,
    readSrc, isa, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
    ↓reduceIte, reduceCtorEq, Nat.reduceLeDiff, and_self, Option.map_some, signExtend_one,
    signExtend_mask, BitVec.ofInt_mul, BitVec.ofInt_toInt,
    lowProduct, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hm : (65535 : BitVec 64).toNat = 65535 := rfl
  have hA := prep_toNat (s.gpr .rax) 65535 hm
  have hB := prep_toNat (s.gpr .rdx) 65535 hm
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩⟩
  · rw [hA, hB, mul_toNat]
    exact reduce _ (Nat.le_trans (Nat.mul_le_mul (residue_le _) (residue_le _)) (by decide)) 65535 hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

end VG.Proof.Idea.X86_64

end

end


/-!
# IDEA on x86-64: a round

`round_run`: round `j` of the code (`Impl.Idea.X86_64.round j`) maps the
state words in `r8`–`r11` (`Holds`) to `Spec.Idea.round` of them under
subkeys `6j … 6j + 5`, read from the schedule at `rdi` (`KeyOk`). It is
composed of runs of its pieces: ⊙ and ⊞ with a subkey (`mulKey_run`,
`addKey_run`), and the multiplication–addition structure.
-/

@[expose] public section

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

tactic_template "run_simp" : tactic => `(tactic| simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
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
  rwa [show 2 * (6 * j + i) = 12 * j + 2 * i by omega_using []] at this

theorem round_run (j : Nat) (hj : j < 8) (z : Spec.Idea.Schedule) (x : Spec.Idea.State)
    (s : State) (hx : Holds x s) (hk : KeyOk z s) :
    ∃ s', runBlock isa (round j) s = some s' ∧
      Holds (Spec.Idea.round (z.getD (6 * j) 0) (z.getD (6 * j + 1) 0) (z.getD (6 * j + 2) 0)
        (z.getD (6 * j + 3) 0) (z.getD (6 * j + 4) 0) (z.getD (6 * j + 5) 0) x) s' ∧
      Keep roundWrites s s' := by
  have k0 := key_at hk j 0 (by omega_using [hj])
  simp only [Nat.mul_zero, Nat.add_zero] at k0
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mulKey_run .r8 (12 * j) s k0.1
  rw [hx.r8, setWidth_setWidth16, k0.2] at v₁
  have hk₁ := hk.keep e₁ (by decide)
  have k3 := key_at hk₁ j 3 (by omega_using [hj])
  simp only [Nat.reduceMul] at k3
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mulKey_run .r11 (12 * j + 6) s₁ k3.1
  rw [e₁.reg .r11 (by decide), hx.r11, setWidth_setWidth16, k3.2] at v₂
  have hk₂ := hk₁.keep e₂ (by decide)
  have k1 := key_at hk₂ j 1 (by omega_using [hj])
  simp only [Nat.mul_one] at k1
  obtain ⟨s₃, h₃, v₃, e₃⟩ := addKey_run (r := .r9) (by decide) (12 * j + 2) s₂ (x.getD 1 0)
    ((e₂.reg .r9 (by decide)).trans ((e₁.reg .r9 (by decide)).trans hx.r9)) k1.1
  rw [k1.2] at v₃
  have hk₃ := hk₂.keep e₃ (by decide)
  have k2 := key_at hk₃ j 2 (by omega_using [hj])
  simp only [Nat.reduceMul] at k2
  obtain ⟨s₄, h₄, v₄, e₄⟩ := addKey_run (r := .r10) (by decide) (12 * j + 4) s₃ (x.getD 2 0)
    ((e₃.reg .r10 (by decide)).trans ((e₂.reg .r10 (by decide)).trans
      ((e₁.reg .r10 (by decide)).trans hx.r10))) k2.1
  rw [k2.2] at v₄
  have hk₄ := hk₃.keep e₄ (by decide)
  have k4 := key_at hk₄ j 4 (by omega_using [hj])
  simp only [Nat.reduceMul] at k4
  obtain ⟨s₅, h₅, a₅, d₅, e₅⟩ := p5_run s₄ (12 * j + 8) k4.1
  obtain ⟨s₆, h₆, v₆, e₆⟩ := mul_run s₅
  have hk₆ := (hk₄.keep e₅ (by decide)).keep e₆ (by decide)
  have k5 := key_at hk₆ j 5 (by omega_using [hj])
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

end

end

/-!
# IDEA on x86-64: a block

`cryptBlock_run`: `Impl.Idea.X86_64.cryptBlock` replaces the block at `rsi`
with `Spec.Idea.cryptBlock` of it under the subkeys at `rdi`: the block's
words are loaded a byte at a time (`load_run`), run through the rounds
(`rounds_run`) and the output transformation (`output_run`), and stored a
byte at a time (`store_run`).
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, ofInt_natCast]

/-! ## Loading -/

theorem loadWord_run {r : Reg} (hr : r ≠ .rax) (hs : r ≠ .rsi) (k : Nat) (s : State) {a : Addr}
    (ha : s.gpr .rsi = a)
    (h0 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k)) 1)
    (h1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k + 1)) 1) :
    ∃ s', runBlock isa (loadWord r k) s = some s' ∧
      s'.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++ s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      Keep [.rax, r] s s' := by
  simp only [loadWord, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc,
    State.load8, isa, Option.map_some, Option.bind_some, ea_at, ha, h0, h1, ↓reduceIte,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
    RegUpd.wr_setFlags, hr, hs.symm, Nat.reduceLeDiff, and_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨bytes16 _ _, keep_reg_of (fun q hq => ?_) rfl rfl rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hq.1, hq.2, ite_false]

/-- The bytes of the block at `a` can be read. -/
def BlockRead (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 i) 1

theorem BlockRead.keep {rs : List Reg} {s s' : State} {a : Addr} (h : BlockRead s a)
    (hk : Keep rs s s') : BlockRead s' a := by
  intro i hi; rw [hk.rd, hk.wr]; exact h i hi

theorem load_run (s : State) {a : Addr} (ha : s.gpr .rsi = a) (hb : BlockRead s a) :
    ∃ s', runBlock isa load s = some s' ∧
      Holds (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem a)) s' ∧
      Keep [.rax, .r8, .r9, .r10, .r11] s s' := by
  have w (k : Nat) (hk : k < 4) := decodeBlock_blockAt s.mem a hk
  obtain ⟨s₁, h₁, v₁, e₁⟩ := loadWord_run (r := .r8) (by decide) (by decide) 0 s ha (hb _ (by decide)) (hb _ (by decide))
  obtain ⟨s₂, h₂, v₂, e₂⟩ := loadWord_run (r := .r9) (by decide) (by decide) 1 s₁
    ((e₁.reg .rsi (by decide)).trans ha) ((hb.keep e₁) _ (by decide)) ((hb.keep e₁) _ (by decide))
  obtain ⟨s₃, h₃, v₃, e₃⟩ := loadWord_run (r := .r10) (by decide) (by decide) 2 s₂
    ((e₂.reg .rsi (by decide)).trans ((e₁.reg .rsi (by decide)).trans ha))
    ((hb.keep e₁ |>.keep e₂) _ (by decide)) ((hb.keep e₁ |>.keep e₂) _ (by decide))
  obtain ⟨s₄, h₄, v₄, e₄⟩ := loadWord_run (r := .r11) (by decide) (by decide) 3 s₃
    ((e₃.reg .rsi (by decide)).trans ((e₂.reg .rsi (by decide)).trans ((e₁.reg .rsi (by decide)).trans ha)))
    ((hb.keep e₁ |>.keep e₂ |>.keep e₃) _ (by decide)) ((hb.keep e₁ |>.keep e₂ |>.keep e₃) _ (by decide))
  refine ⟨s₄, run_append (run_append (run_append h₁ h₂) h₃) h₄, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [e₄.reg .r8 (by decide), e₃.reg .r8 (by decide), e₂.reg .r8 (by decide), v₁, w 0 (by decide)]
  · rw [e₄.reg .r9 (by decide), e₃.reg .r9 (by decide), v₂, e₁.mem, w 1 (by decide)]
  · rw [e₄.reg .r10 (by decide), v₃, e₂.mem, e₁.mem, w 2 (by decide)]
  · rw [v₄, e₃.mem, e₂.mem, e₁.mem, w 3 (by decide)]
  · exact (e₁.mono (by decide)).trans ((e₂.mono (by decide)).trans ((e₃.mono (by decide)).trans
      (e₄.mono (by decide))))

/-! ## The rounds -/

theorem rounds_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) :
    ∀ n ≤ 8, ∀ s : State, Holds x s → KeyOk z s →
      ∃ s', runBlock isa ((List.range n).flatMap round) s = some s' ∧
        Holds (roundsSpec z n x) s' ∧ Keep roundWrites s s'
  | 0, _, s, hx, _ => ⟨s, by simp [runBlock_nil], hx, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | n + 1, hn, s, hx, hk => by
    obtain ⟨s₁, h₁, x₁, e₁⟩ := rounds_run z x n (by omega_using [hn]) s hx hk
    obtain ⟨s₂, h₂, x₂, e₂⟩ := round_run n (by omega_using [hn]) z _ s₁ x₁ (hk.keep e₁ (by decide))
    refine ⟨s₂, ?_, ?_, e₁.trans e₂⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append h₁ h₂
    · simp only [roundsSpec, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact x₂

/-! ## The output transformation -/

/-- The output words: `Y₁` in `r8`, `Y₂` in `r10`, `Y₃` in `r9`, `Y₄` in `r11`. -/
structure OutHolds (y : Spec.Idea.State) (s : State) : Prop where
  r8 : s.gpr .r8 = (y.getD 0 0).setWidth 64
  r10 : s.gpr .r10 = (y.getD 1 0).setWidth 64
  r9 : s.gpr .r9 = (y.getD 2 0).setWidth 64
  r11 : s.gpr .r11 = (y.getD 3 0).setWidth 64

theorem out1_run (s : State) (hk : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi 96)) 8) :
    ∃ s', runBlock isa [.mov .rax (.reg .r11), .mov .rdx (.mem (at_ .rdi 96)), .shift .shr .rdx 48] s =
        some s' ∧
      s'.gpr .rax = s.gpr .r11 ∧ s'.gpr .rdx = s.mem.readW (s.ea (at_ .rdi 96)) 64 >>> 48 ∧
      Keep [.rax, .rdx] s s' := by
  simp only [State.ea, at_] at hk ⊢
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc, State.load64,
    isa, Option.map_some, State.ea, hk, ↓reduceIte, Nat.reduceLeDiff, and_self,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq, Option.some.injEq, exists_eq_left',
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, true_and]
  refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hq.1, hq.2, ite_false]

theorem out2_run (s : State) (hk : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi 96)) 8) :
    ∃ s', runBlock isa [.mov .r11 (.reg .rdx),
        .mov .rdx (.mem (at_ .rdi 96)), .shift .shr .rdx 16, .alu .add .r10 (.reg .rdx),
        .alu .and .r10 (.imm 0xffff),
        .mov .rdx (.mem (at_ .rdi 96)), .shift .shr .rdx 32, .alu .add .r9 (.reg .rdx),
        .alu .and .r9 (.imm 0xffff)] s = some s' ∧
      s'.gpr .r11 = s.gpr .rdx ∧
      s'.gpr .r10 = (s.gpr .r10 + (s.mem.readW (s.ea (at_ .rdi 96)) 64 >>> 16)) &&& 65535 ∧
      s'.gpr .r9 = (s.gpr .r9 + (s.mem.readW (s.ea (at_ .rdi 96)) 64 >>> 32)) &&& 65535 ∧
      Keep [.rdx, .r9, .r10, .r11] s s' := by
  simp only [State.ea, at_] at hk ⊢
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc,
    State.load64, isa, Option.map_some, Option.bind_some, State.ea, hk, ↓reduceIte,
    Nat.reduceLeDiff, and_self, signExtend_mask,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, reduceCtorEq, Option.some.injEq,
    exists_eq_left', RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags,
    RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, true_and]
  refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hq.1, hq.2.1, hq.2.2.1,
    hq.2.2.2, ite_false]

theorem output_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x s)
    (hk : KeyOk z s) :
    ∃ s', runBlock isa output s = some s' ∧
      OutHolds (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) x) s' ∧
      Keep roundWrites s s' := by
  have k48 := hk.low 48 (by decide)
  simp only [Nat.reduceMul] at k48
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mulKey_run .r8 96 s k48.1
  rw [hx.r8, setWidth_setWidth16, k48.2] at v₁
  have hk₁ := hk.keep e₁ (by decide)
  have k₁ := hk₁.low 48 (by decide)
  simp only [Nat.reduceMul] at k₁
  obtain ⟨s₂, h₂, a₂, d₂, e₂⟩ := out1_run s₁ k₁.1
  obtain ⟨s₃, h₃, v₃, e₃⟩ := mul_run s₂
  have hk₃ := (hk₁.keep e₂ (by decide)).keep e₃ (by decide)
  have k₃ := hk₃.low 48 (by decide)
  simp only [Nat.reduceMul] at k₃
  obtain ⟨s₄, h₄, r11₄, r10₄, r9₄, e₄⟩ := out2_run s₃ k₃.1
  have l1 := hk₃.last 1 (by decide)
  have l2 := hk₃.last 2 (by decide)
  have l3 := hk₁.last 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at l1 l2 l3
  refine ⟨s₄, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [output]
    exact run_append (run_append (run_append h₁ h₂) h₃) h₄
  · rw [e₄.reg .r8 (by decide), e₃.reg .r8 (by decide), e₂.reg .r8 (by decide), v₁, output_getD0]
  · rw [r10₄, e₃.reg .r10 (by decide), e₂.reg .r10 (by decide), e₁.reg .r10 (by decide), hx.r10,
      add_mask, l1, output_getD1]
  · rw [r9₄, e₃.reg .r9 (by decide), e₂.reg .r9 (by decide), e₁.reg .r9 (by decide), hx.r9,
      add_mask, l2, output_getD2]
  · rw [r11₄, v₃, a₂, d₂, e₁.reg .r11 (by decide), hx.r11, setWidth_setWidth16, l3, output_getD3]
  · exact (e₁.weaken (by decide)).trans ((e₂.weaken (by decide)).trans ((e₃.weaken (by decide)).trans
      (e₄.weaken (by decide))))

/-! ## Storing -/

theorem storeWord_run (r : Reg) (k : Nat) (s : State) {a : Addr}
    (ha : s.gpr .rsi = a)
    (h1 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k + 1)) 1)
    (h0 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k)) 1) :
    ∃ s', runBlock isa (storeWord r k) s = some s' ∧
      s'.mem = (s.mem.writeW (a + BitVec.ofNat 64 (2 * k + 1)) ((s.gpr r).setWidth 8)).writeW
        (a + BitVec.ofNat 64 (2 * k)) ((s.gpr r >>> 8).setWidth 8) ∧
      (∀ q, q ≠ .rax → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [storeWord, runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc,
    State.store8, isa, Option.map_some, ea_at, ha, h0, h1, ↓reduceIte,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, Nat.reduceLeDiff, and_self, reduceCtorEq,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
    RegUpd.wr_setFlags, Option.some.injEq, exists_eq_left', true_and]
  exact ⟨fun q hq => by simp only [hq, ite_false], trivial⟩

/-- The bytes of the block at `a` can be written. -/
def BlockWrite (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions s.wr (a + BitVec.ofNat 64 i) 1

theorem frame_write8 {a : Addr} {m m' : Mem} {j : Nat} (v : BitVec 8) (hj : j < 8)
    (h : Frame [⟨a, 8⟩] m m') : Frame [⟨a, 8⟩] m (m'.writeW (a + BitVec.ofNat 64 j) v) :=
  h.writeW (List.mem_singleton_self _) v (Offset.contains_base a (by omega_using [hj]) (by omega_using [hj]))

theorem store_run (y : Spec.Idea.State) (s : State) {a : Addr} (ha : s.gpr .rsi = a)
    (hw : BlockWrite s a) (hy : OutHolds y s) :
    ∃ s', runBlock isa store s = some s' ∧
      Spec.Idea.blockAt s'.mem a = Spec.Idea.encodeBlock y ∧
      Frame [⟨a, 8⟩] s.mem s'.mem ∧ (∀ q, q ≠ .rax → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, h₁, m₁, g₁, rd₁, wr₁⟩ := storeWord_run .r8 0 s ha (hw _ (by decide)) (hw _ (by decide))
  have ha₁ : s₁.gpr .rsi = a := (g₁ .rsi (by decide)).trans ha
  have hw₁ : BlockWrite s₁ a := fun i hi => wr₁ ▸ hw i hi
  obtain ⟨s₂, h₂, m₂, g₂, rd₂, wr₂⟩ := storeWord_run .r10 1 s₁ ha₁ (hw₁ _ (by decide)) (hw₁ _ (by decide))
  have ha₂ : s₂.gpr .rsi = a := (g₂ .rsi (by decide)).trans ha₁
  have hw₂ : BlockWrite s₂ a := fun i hi => wr₂ ▸ hw₁ i hi
  obtain ⟨s₃, h₃, m₃, g₃, rd₃, wr₃⟩ := storeWord_run .r9 2 s₂ ha₂ (hw₂ _ (by decide)) (hw₂ _ (by decide))
  have ha₃ : s₃.gpr .rsi = a := (g₃ .rsi (by decide)).trans ha₂
  have hw₃ : BlockWrite s₃ a := fun i hi => wr₃ ▸ hw₂ i hi
  obtain ⟨s₄, h₄, m₄, g₄, rd₄, wr₄⟩ := storeWord_run .r11 3 s₃ ha₃ (hw₃ _ (by decide)) (hw₃ _ (by decide))
  have v10 : s₁.gpr .r10 = (y.getD 1 0).setWidth 64 := (g₁ .r10 (by decide)).trans hy.r10
  have v9 : s₂.gpr .r9 = (y.getD 2 0).setWidth 64 :=
    (g₂ .r9 (by decide)).trans ((g₁ .r9 (by decide)).trans hy.r9)
  have v11 : s₃.gpr .r11 = (y.getD 3 0).setWidth 64 :=
    (g₃ .r11 (by decide)).trans ((g₂ .r11 (by decide)).trans ((g₁ .r11 (by decide)).trans hy.r11))
  rw [v11] at m₄
  rw [v9] at m₃
  rw [v10] at m₂
  rw [hy.r8] at m₁
  rw [m₃, m₂, m₁] at m₄
  refine ⟨s₄, run_append (run_append (run_append h₁ h₂) h₃) h₄, ?_, ?_,
    fun q hq => (g₄ q hq).trans ((g₃ q hq).trans ((g₂ q hq).trans (g₁ q hq))),
    rd₄.trans (rd₃.trans (rd₂.trans rd₁)), wr₄.trans (wr₃.trans (wr₂.trans wr₁))⟩
  · apply Vector.ext
    intro i hi
    simp only [Spec.Idea.blockAt, Vector.getElem_ofFn, m₄, encodeBlock_get _ hi]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
        i = 5 ∨ i = 6 ∨ i = 7 := by omega_using [hi]
    all_goals simp (disch := decide) only [write8_apply, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte, lo8, hi8, BitVec.ushiftRight_zero]
  · rw [m₄]
    repeat' apply frame_write8 _ (by decide)
    exact Frame.refl _ _

/-! ## A block -/

theorem cryptBlock_run (z : Spec.Idea.Schedule) (s : State) {a : Addr} (ha : s.gpr .rsi = a)
    (hb : BlockRead s a) (hw : BlockWrite s a) (hk : KeyOk z s) :
    ∃ s', runBlock isa cryptBlock s = some s' ∧
      Spec.Idea.blockAt s'.mem a = Spec.Idea.cryptBlock z (Spec.Idea.blockAt s.mem a) ∧
      Frame [⟨a, 8⟩] s.mem s'.mem ∧ (∀ q, q ∉ roundWrites → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, h₁, x₁, e₁⟩ := load_run s ha hb
  have k₁ := hk.keep e₁ (by decide)
  obtain ⟨s₂, h₂, x₂, e₂⟩ := rounds_run z _ 8 (by decide) s₁ x₁ k₁
  obtain ⟨s₃, h₃, x₃, e₃⟩ := output_run z _ s₂ x₂ (k₁.keep e₂ (by decide))
  have e₁₃ := ((e₁.weaken (by decide)).trans e₂).trans e₃
  obtain ⟨s₄, h₄, b₄, f₄, g₄, rd₄, wr₄⟩ := store_run _ s₃ ((e₁₃.reg .rsi (by decide)).trans ha)
    (fun i hi => e₁₃.wr ▸ hw i hi) x₃
  refine ⟨s₄, ?_, ?_, ?_, fun q hq => ?_, rd₄.trans e₁₃.rd, wr₄.trans e₁₃.wr⟩
  · simp only [cryptBlock]
    exact run_append (run_append (run_append h₁ h₂) h₃) h₄
  · rw [b₄, Spec.Idea.cryptBlock, crypt_eq]
  · rw [← e₁₃.mem]; exact f₄
  · rw [g₄ q (by intro h; subst h; exact hq (by decide)), e₁₃.reg q hq]

end VG.Proof.Idea.X86_64
