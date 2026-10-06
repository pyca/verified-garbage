import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
import VerifiedGarbage.Proof.X448.X86_64.Env
import VerifiedGarbage.Proof.Ed448.Formulas

/-!
# Ed448 base-point multiplication on x86-64: field programs

A list of field operations on the slots (`FOp`) runs as X448's verified
field arithmetic (`mulE`, `sqrE`, `addE`, `subE`), for any correct field
multiplications (`FieldOk`): the slots become the operations' evaluation
(`evalOps`), and nothing else changes but the registers `clob` and the
memory in `[64, 1648)`. What the doubling and the addition programs evaluate
to is target-independent (`Proof/Ed448/Formulas.lean`).
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk mulE sqrE addE subE)

theorem slot_idx {n : Nat} (h : n < 22) : Impl.X448.X86_64.slot n = Impl.X448.X86_64.slot (idx n).val := by
  simp only [idx, Nat.mod_eq_of_lt h]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem fop_ok {s : State} {base : Addr} (hs : Scr s base) (op : FOp) (hv : fopValid op) :
    WP isa (.block (fopCode fld op)) s fun t =>
      Keep base s t ∧ E t.mem base = evalOp op (E s.mem base) := by
  cases op with
  | mul o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [fopCode, slot_idx h1, slot_idx h2, slot_idx h3]
    exact mulE hf hs _ _ _
  | sqr o a =>
    obtain ⟨h1, h2⟩ := hv
    simp only [fopCode, slot_idx h1, slot_idx h2]
    exact sqrE hf hs _ _
  | add o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [fopCode, slot_idx h1, slot_idx h2, slot_idx h3]
    exact addE hs _ _ _
  | sub o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [fopCode, slot_idx h1, slot_idx h2, slot_idx h3]
    exact subE hs _ _ _

include hf in
theorem fieldCode_ok (ops : List FOp) (hv : ∀ op ∈ ops, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) :
    WP isa (.block (fieldCode fld ops)) s fun t =>
      Keep base s t ∧ E t.mem base = evalOps ops (E s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fop_ok hf hs op (hv op List.mem_cons_self)) fun t ⟨ht, et⟩ => ?_
    refine WP.mono (ih (fun o h => hv o (List.mem_cons_of_mem _ h)) (ht.scr hs))
      fun u ⟨hu, eu⟩ => ⟨ht.trans hu, by rw [eu, et, evalOps, evalOps, List.foldl_cons]⟩

end VG.Proof.Ed448.X86_64
