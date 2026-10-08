import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Memory

/-! # Public cursor updates and loop conditions -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64

theorem next8_ok (s : State) (n : BitVec 32) :
    WP isa (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8), .alu .cmp .r9 (.imm n)]) s
      fun t => t.gpr .rdx = s.gpr .rdx + 128 ∧ t.gpr .r9 = s.gpr .r9 - 8 ∧
        t.cf = some (decide ((s.gpr .r9 - 8).toNat < (n.signExtend 64).toNat)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → t.gpr r = s.gpr r) ∧ (∀ r l, t.lane r l = s.lane r l) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

theorem cmp8_ok (s : State) (n : BitVec 32) :
    WP isa (.block [.alu .cmp .r9 (.imm n)]) s fun t =>
      t.cf = some (decide ((s.gpr .r9).toNat < (n.signExtend 64).toNat)) ∧ YFrame [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, isa, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
