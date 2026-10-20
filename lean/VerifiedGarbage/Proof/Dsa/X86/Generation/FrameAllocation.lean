module
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext

/-! # Release a stack frame after the body proves its stack pointer is restored -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Dsa.X86

theorem alloc_restored {bytes : Nat} {body : Prog isa} {s : State} {Q : State → Prop}
    (size : 0 < bytes ∧ bytes < 4096 ∧ bytes % 4 = 0) (room : bytes ≤ (s.gpr .esp).toNat)
    (run : WP isa body (allocated bytes s) fun t =>
      t.gpr .esp = (allocated bytes s).gpr .esp ∧ Q (freed bytes t)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨trace, t, exec, sp, result⟩ := run
  obtain ⟨_, wr⟩ := Exec.rdwr exec
  have push : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, VG.X86.push, size.1, size.2.1, size.2.2, room, and_self, ite_true]
    rfl
  have pop : isa.pop (.free bytes) (allocated bytes s) t = some (freed bytes t) := by
    simp only [isa, VG.X86.pop]
    refine ite_eq_left ⟨size.1, size.2.1, size.2.2, sp, wr, ?_⟩
    rfl
  exact ⟨_, _, Exec.frame push exec pop, result⟩
end VG.Proof.Dsa.X86.Generation
