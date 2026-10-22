module

public import VerifiedGarbage.Proof.Framework.Semantics

/-! Shared instruction-wise consequences of structured code audits. -/

@[expose] public section
namespace VG

/-- `Code.all p` holds of every instruction. -/
theorem Code.all_instrs {I C : Type} {p : I → Bool} {c : Code I C} (h : c.all p = true) :
    ∀ i ∈ instrs c, p i = true := by
  induction c with
  | block is => simpa [Code.all, instrs, List.all_eq_true] using h
  | seq a b iha ihb =>
    simp only [Code.all, Bool.and_eq_true] at h
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    exacts [iha h.1 i hi, ihb h.2 i hi]
  | ite _ t e iht ihe =>
    simp only [Code.all, Bool.and_eq_true] at h
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    exacts [iht h.1 i hi, ihe h.2 i hi]
  | loop b _ ih => exact ih h
  | call _ b ih => exact ih h
  | frame x b y ih =>
    simp only [Code.all, Bool.and_eq_true] at h
    intro i hi
    simp only [instrs, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | hi | rfl
    exacts [h.1.1, ih h.1.2 i hi, h.2]


end VG
