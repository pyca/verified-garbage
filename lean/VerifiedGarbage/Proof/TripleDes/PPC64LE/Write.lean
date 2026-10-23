module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # Reading a PPC64LE state through register writes -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE

theorem gpr_write (s : State) (d : Reg) (v : BitVec 64) (r : Reg) :
    (s.write d v).gpr r = if r = d then v else s.gpr r := rfl

theorem gpr_write_self (s : State) (d : Reg) (v : BitVec 64) : (s.write d v).gpr d = v := by
  simp [State.write]

theorem gpr_write_of_ne (s : State) {d r : Reg} (v : BitVec 64) (h : r ≠ d) :
    (s.write d v).gpr r = s.gpr r := by
  simp [State.write, h]

theorem mem_write (s : State) (d : Reg) (v : BitVec 64) : (s.write d v).mem = s.mem := rfl
theorem rd_write (s : State) (d : Reg) (v : BitVec 64) : (s.write d v).rd = s.rd := rfl
theorem wr_write (s : State) (d : Reg) (v : BitVec 64) : (s.write d v).wr = s.wr := rfl

/-- `s'` is `s` but for the registers `written`. -/
structure Kept (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Kept.trans {rs : List Reg} {s s' s'' : State}
    (h : Kept rs s s') (h' : Kept rs s' s'') : Kept rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

end VG.Proof.TripleDes.PPC64LE
