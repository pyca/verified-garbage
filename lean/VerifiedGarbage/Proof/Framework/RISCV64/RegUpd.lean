module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# RISC-V: register reads through writes

Untrusted: everything here is checked by Lean. The lemmas symbolic
execution reads registers with after `State.write` (`gpr_write`, an `if`
decided for literal registers, or `gpr_write_self` and `gpr_write_of_ne` for
variables), without unfolding the write into a function on registers, the
other fields a write keeps, and how writes to the same or different
registers combine (`write_write`, `write_comm`).
-/

@[expose] public section

namespace VG.RISCV64.RegUpd

variable (s : State)

theorem gpr_write (r : Reg) (v : BitVec 64) (r' : Reg) :
    (s.write r v).gpr r' = if r' = r then v else s.gpr r' := rfl

theorem gpr_write_self (r : Reg) (v : BitVec 64) : (s.write r v).gpr r = v := by
  simp [State.write]

theorem gpr_write_of_ne {r r' : Reg} (v : BitVec 64) (h : ¬r' = r) :
    (s.write r v).gpr r' = s.gpr r' := by
  simp [State.write, h]

theorem mem_write (r : Reg) (v : BitVec 64) : (s.write r v).mem = s.mem := rfl
theorem rd_write (r : Reg) (v : BitVec 64) : (s.write r v).rd = s.rd := rfl
theorem wr_write (r : Reg) (v : BitVec 64) : (s.write r v).wr = s.wr := rfl
theorem sp_write (r : Reg) (v : BitVec 64) : (s.write r v).sp = s.sp := rfl
theorem unknowns_write (r : Reg) (v : BitVec 64) : (s.write r v).unknowns = s.unknowns := rfl

theorem write_write (r : Reg) (v w : BitVec 64) : (s.write r v).write r w = s.write r w := by
  simp only [State.write, State.mk.injEq, and_true]
  funext r'; split <;> rfl

theorem write_comm {r r' : Reg} (h : r ≠ r') (v w : BitVec 64) :
    (s.write r v).write r' w = (s.write r' w).write r v := by
  simp only [State.write, State.mk.injEq, and_true]
  funext x
  by_cases h₁ : x = r'
  · subst h₁; simp [Ne.symm h]
  · simp [h₁]

/-- A write to a register leaves memory as it was, in a state with other
memory. -/
theorem write_mem (r : Reg) (v : BitVec 64) (m : Mem) :
    { s.write r v with mem := m } = { s with mem := m }.write r v := rfl

end VG.RISCV64.RegUpd
