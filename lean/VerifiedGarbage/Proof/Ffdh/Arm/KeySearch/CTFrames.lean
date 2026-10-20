module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Reserving and releasing the nested attempt's argument frame adds no
memory accesses to its body's trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm

theorem alloc_ct {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (bodyCT : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) (fun _ _ => True) := by
  intro s t ts tt u v h es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocated bytes a := by
    intro a b push
    simp only [isa, VG.Arm.push] at push
    split at push <;> cases push
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have first := alloc_eq ps
      have second := alloc_eq pt
      subst first second
      obtain ⟨trace, _⟩ := bodyCT _ _ _ _ _ _ ⟨s, t, h, rfl, rfl⟩ bs bt
      refine ⟨?_, trivial⟩
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using trace

end VG.Proof.Ffdh.Arm.KeySearch
