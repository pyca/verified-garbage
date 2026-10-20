module
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo

/-! # Allocating and freeing a fixed stack frame introduces no memory accesses -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

theorem allocated_push {bytes : Nat} {s : State}
    (size : 0 < bytes ∧ bytes < 4096 ∧ bytes % 4 = 0) (room : bytes ≤ (s.gpr .esp).toNat) :
    isa.push (.alloc bytes) s = some (allocated bytes s) := by
  simp only [isa, push, size.1, size.2.1, size.2.2, room, and_self, ite_true]
  rfl

theorem allocation_ct {α : Type} {Φ : α → State → Prop} {Ψ : α → State → Prop}
    {bytes : Nat} {body : Prog isa} (size : 0 < bytes ∧ bytes < 4096 ∧ bytes % 4 = 0)
    (room : ∀ p s, Φ p s → bytes ≤ (s.gpr .esp).toNat)
    (enter : ∀ p s, Φ p s → Ψ p (allocated bytes s))
    (ct : RelCT isa (Two Ψ) body (fun _ _ => True)) :
    RelCT isa (Two Φ) (.frame (.alloc bytes) body (.free bytes)) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
  cases es with
  | frame ps bs _ =>
    cases et with
    | frame pt bt _ =>
      rw [allocated_push size (room p s hs), Option.some.injEq] at ps
      rw [allocated_push size (room p t ht), Option.some.injEq] at pt
      subst ps pt
      have h := (ct _ _ _ _ _ _ ⟨p, enter p s hs, enter p t ht⟩ bs bt).1
      exact ⟨by simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using h, trivial⟩
end VG.Proof.Dsa.X86.Generation
