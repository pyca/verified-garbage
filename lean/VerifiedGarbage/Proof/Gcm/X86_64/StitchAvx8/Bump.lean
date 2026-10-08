import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Buffer

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd

theorem bump_ok (s : State) :
    WP isa (.block [.alu32 .add .r8 (.imm 8)]) s fun t =>
      (t.gpr .r8).setWidth 32 = (s.gpr .r8).setWidth 32 + 8 ∧
      (∀ r, r ≠ .r8 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
      (∀ r l, t.lane r l = s.lane r l) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    execAlu32, readSrc32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.setReg32, gpr_setReg, ite_true, setWidth_setWidth_32]
  · intro r hr; simp only [State.setReg32, gpr_setReg, gpr_arithFlags, hr, ite_false]
  · simp only [State.setReg32, mem_setReg, mem_arithFlags]
  · intro r l
    simp only [State.lane, State.setReg32, xmm_setReg, xmm_arithFlags,
      ymmHi_setReg, ymmHi_arithFlags]
  · simp only [State.setReg32, rd_setReg, rd_arithFlags]
  · simp only [State.setReg32, wr_setReg, wr_arithFlags]

end VG.Proof.Gcm.X86_64.StitchAvx8
