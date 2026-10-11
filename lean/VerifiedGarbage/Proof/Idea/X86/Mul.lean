import VerifiedGarbage.Proof.Idea.Arith32
import VerifiedGarbage.Impl.Idea.X86
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# IDEA on x86 (32-bit): ⊙ without branches

`mul_run`: `mulCode src` leaves `eax ⊙ src` (of their low 16 bits) in
`edx`, and changes nothing but `eax`, `edx` and the flags, if `src` reads
the same value once `eax` has changed. The arithmetic is
`Proof.Idea.prep32_toNat` and `Proof.Idea.reduce32`.
-/

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

/-- What a block keeps: every register but `written`, memory and regions. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r fun hm => hr (hs r hm), h.mem, h.rd, h.wr⟩

/-- `Keep.mono` for literal lists, by evaluation. -/
theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : (rs.all fun r => rs'.contains r) = true) : Keep rs' s s' :=
  h.mono fun r hr => by
    have := List.all_eq_true.mp hs r hr
    simpa using this

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil, Option.bind_some]
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem run_append {a b : List Instr} {s s₁ s₂ : State}
    (h₁ : runBlock isa a s = some s₁) (h₂ : runBlock isa b s₁ = some s₂) :
    runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_append, h₁, Option.bind_some, h₂]

macro "keep_tac" : tactic => `(tactic| (
  refine ⟨fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hq, ite_false]))

/-- A source that reads `v` from any state agreeing with `s` but on `eax`. -/
def SrcOk (s : State) (src : Src) (v : BitVec 32) : Prop :=
  ∀ t : State, t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → (∀ r, r ≠ .eax → t.gpr r = s.gpr r) →
    readSrc t src = some v

theorem mul_ofNat32 (x y : BitVec 32) : x * y = BitVec.ofNat 32 (x.toNat * y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]

theorem mul_run (src : Src) (v : BitVec 32) (s : State) (hsrc : SrcOk s src v) :
    ∃ s', runBlock isa (mulCode src) s = some s' ∧
      s'.gpr .edx = (Spec.Idea.mul ((s.gpr .eax).setWidth 16) (v.setWidth 16)).setWidth 32 ∧
      Keep [.eax, .edx] s s' := by
  have hm : (65535 : BitVec 32).toNat = 65535 := rfl
  -- The first operand's residue.
  obtain ⟨s₁, h₁, v₁, e₁⟩ : ∃ s₁, runBlock isa [.alu .sub .eax (.imm 1), .alu .and .eax (.imm 0xffff),
      .alu .add .eax (.imm 1)] s = some s₁ ∧ s₁.gpr .eax = ((s.gpr .eax - 1) &&& 65535) + 1 ∧
      Keep [.eax] s s₁ := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, Option.bind_some,
      RegUpd.gpr_setReg, ↓reduceIte, Option.some.injEq, exists_eq_left', true_and]
    keep_tac
  have hv : readSrc s₁ src = some v := hsrc s₁ e₁.mem e₁.rd e₁.wr fun r hr => e₁.reg r (by simpa using hr)
  refine ⟨_, run_append (a := [_, _, _]) h₁ (by
    rw [runBlock_cons, show exec (.mov .edx src) s₁ = some (s₁.setReg .edx v) by simp [exec, hv],
      runStep_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, execShift, execMul,
      readSrc, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
      ↓reduceIte, reduceCtorEq, Nat.reduceLeDiff, and_self, Option.map_some]
    rfl), ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg, ↓reduceIte]
    have hA := prep32_toNat (s.gpr .eax) 65535 hm
    have hB := prep32_toNat v 65535 hm
    have hp₀ := Nat.mul_le_mul (residue_pos ((s.gpr .eax).setWidth 16)) (residue_pos (v.setWidth 16))
    have hp := Nat.mul_le_mul (residue_le ((s.gpr .eax).setWidth 16)) (residue_le (v.setWidth 16))
    rw [mul32_toNat]
    refine reduce32 _ hp₀ (Nat.le_trans hp (by decide)) _ 65535 1 ?_ hm rfl
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, v₁, hA, hB]
    show (2 ^ 32 - 1 + _ % 2 ^ 32) % 2 ^ 32 = _
    have := Nat.le_trans hp (show 2 ^ 16 * 2 ^ 16 ≤ 2 ^ 32 by decide)
    have := Nat.le_trans (show 1 ≤ 1 * 1 by decide) hp₀
    omega
  · refine e₁.weaken (rs' := [.eax, .edx]) (by decide) |>.trans ⟨fun q hq => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hq.1, hq.2, ite_false]

end VG.Proof.Idea.X86
