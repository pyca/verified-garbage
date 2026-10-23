module

public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# PPC64LE: register reads through writes

Untrusted: everything here is checked by Lean. The lemmas symbolic
execution reads registers with after `State.write` (`gpr_write_self`,
`gpr_write_of_ne`), without unfolding the write into a function on
registers, and the other fields a write keeps; and `exec_ld`/`exec_std`,
the doubleword load and store at an offset, with the side conditions in the
order the proofs ported from AArch64 state them, and likewise `exec_addi'`,
`exec_subi'` and `exec_or_self` (`mr`).
-/

@[expose] public section

namespace VG.PPC64LE.RegUpd

variable (s : State)

theorem gpr_write_self (r : Reg) (v : BitVec 64) : (s.write r v).gpr r = v := by
  simp [State.write]

theorem gpr_write_of_ne {r r' : Reg} (v : BitVec 64) (h : ¬r' = r) : (s.write r v).gpr r' = s.gpr r' := by
  simp [State.write, h]

theorem mem_write (r : Reg) (v : BitVec 64) : (s.write r v).mem = s.mem := rfl
theorem rd_write (r : Reg) (v : BitVec 64) : (s.write r v).rd = s.rd := rfl
theorem wr_write (r : Reg) (v : BitVec 64) : (s.write r v).wr = s.wr := rfl
theorem sp_write (r : Reg) (v : BitVec 64) : (s.write r v).sp = s.sp := rfl
theorem lr_write (r : Reg) (v : BitVec 64) : (s.write r v).lr = s.lr := rfl

end VG.PPC64LE.RegUpd

namespace VG.PPC64LE

/-- `ld t, off(n)`. -/
theorem exec_ld {s : State} {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) (hn : n ≠ .r0 := by decide) :
    exec (.load .d t n off) s = some (s.write t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)) :=
  exec_load_d hn ⟨ho.2, by omega⟩ h

/-- `std t, off(n)`. -/
theorem exec_std {s : State} {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) (hn : n ≠ .r0 := by decide) :
    exec (.store .d t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t) } :=
  exec_store_d hn ⟨ho.2, by omega⟩ h

/-- `addi d, n, imm`. -/
theorem exec_addi' {s : State} {d n : Reg} {imm : Nat} (h : imm < 32768) (hn : n ≠ .r0 := by decide) :
    exec (.addi d n imm) s = some (s.write d (s.gpr n + BitVec.ofNat 64 imm)) :=
  exec_addi hn h

/-- `subi d, n, imm`. -/
theorem exec_subi' {s : State} {d n : Reg} {imm : Nat} (h : imm < 32768) (hn : n ≠ .r0 := by decide) :
    exec (.subi d n imm) s = some (s.write d (s.gpr n - BitVec.ofNat 64 imm)) :=
  exec_subi hn (by omega)

/-- `mr d, n` (`or d, n, n`). -/
theorem exec_or_self {s : State} {d n : Reg} :
    exec (.logic .or d n n) s = some (s.write d (s.gpr n)) := by
  rw [exec_logic]; simp only [BitVec.or_self]

end VG.PPC64LE
