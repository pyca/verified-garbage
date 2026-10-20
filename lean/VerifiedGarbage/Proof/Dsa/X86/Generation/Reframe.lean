module
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Lift helpers from exact subarena permissions to the caller's larger arena

Unlike a no-call narrowing lemma, this also covers hash helpers with stack
frames. The helper's postcondition supplies its restored permissions.
-/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86

theorem wp_reframe {code : Prog isa} {s : State} {rd wr : List Region} {P : State → Prop}
    (run : WP isa code (s.withRegions rd wr) P)
    (read : Covers (rd ++ wr) (s.rd ++ s.wr)) (write : Covers wr s.wr)
    (restored : ∀ t, P t → t.rd = rd ∧ t.wr = wr) {Q : State → Prop}
    (finish : ∀ t, t.rd = s.rd → t.wr = s.wr → P (t.withRegions rd wr) → Q t) : WP isa code s Q := by
  obtain ⟨trace, t, exec, post⟩ := run
  have lifted := VG.X86.Exec.widen exec read write
  rw [State.withRegions_withRegions, State.withRegions_self] at lifted
  refine ⟨trace, t.withRegions s.rd s.wr, lifted, finish _ rfl rfl ?_⟩
  rw [State.withRegions_withRegions]
  obtain ⟨r, w⟩ := restored t post
  rw [← r, ← w, State.withRegions_self]
  exact post

theorem keeps_reframe {s t : State} {rd wr : List Region} {regs : List Reg}
    (read : t.rd = s.rd) (write : t.wr = s.wr)
    (K : Keeps regs (s.withRegions rd wr) (t.withRegions rd wr)) : Keeps regs s t :=
  ⟨K.1, read, write⟩
end VG.Proof.Dsa.X86.Generation
