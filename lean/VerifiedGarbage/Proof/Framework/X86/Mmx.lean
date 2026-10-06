import VerifiedGarbage.TCB.X86.Isa

/-!
# x86 MMX instructions: what they change

An MMX instruction (`TCB/X86/Mmx.lean`) writes only an MMX or XMM register.
-/

namespace VG.X86

theorem MOp.exec_eq {op : MOp} {s s' : State} (h : op.exec s = some s') :
    s' = { s with mm := s'.mm, xmm := s'.xmm } := by
  cases op with
  | bin o d src | movq d src =>
    simp only [MOp.exec] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨v, -, rfl⟩ := h
      rfl
    · cases h
  | shift _ _ _ | punpckldq _ _ | movd _ _ | movq2dq _ _ | movdq2q _ _ =>
    simp only [MOp.exec] at h
    split at h
    · cases h; rfl
    · cases h

end VG.X86
