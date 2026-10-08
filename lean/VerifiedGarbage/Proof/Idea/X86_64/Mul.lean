import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Impl.Idea.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# IDEA on x86-64: ⊙ without branches

`mul_run`: `mulCode` leaves `rax ⊙ rdx` (of their low 16 bits) in `rdx`,
and changes nothing but `rax`, `rdx` and the flags. The arithmetic is
`prep_toNat` (the operands' residues) and `reduce` (the product modulo
2¹⁶ + 1 from its halves, corrected by the sign of their difference).
-/

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

/-- `mulCode` on the machine. -/
theorem mul_run (s : State) : ∃ s', runBlock isa mulCode s = some s' ∧
    s'.gpr .rdx = (Spec.Idea.mul ((s.gpr .rax).setWidth 16) ((s.gpr .rdx).setWidth 16)).setWidth 64 ∧
    Keep [.rax, .rdx] s s' := by
  simp only [mulCode, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, execMul,
    readSrc, isa, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
    ↓reduceIte, reduceCtorEq, Nat.reduceLeDiff, and_self, Option.map_some, signExtend_one,
    signExtend_mask, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hm : (65535 : BitVec 64).toNat = 65535 := rfl
  have hA := prep_toNat (s.gpr .rax) 65535 hm
  have hB := prep_toNat (s.gpr .rdx) 65535 hm
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩⟩
  · rw [hA, hB, mul_toNat]
    exact reduce _ (Nat.le_trans (Nat.mul_le_mul (residue_le _) (residue_le _)) (by decide)) 65535 hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

end VG.Proof.Idea.X86_64
