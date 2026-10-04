import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
import VerifiedGarbage.Proof.X448.AArch64.Weak.Ops
import VerifiedGarbage.Proof.Ed448.Formulas

/-!
# Ed448 base-point multiplication on AArch64: field programs

A list of field operations on the slots (`FOp`) runs as X448's field
arithmetic on AArch64 (`mulE`, `addE`, `subE`): the slots become the
operations' evaluation (`evalOps`, `Proof/Ed448/Formulas.lean`), their limbs
stay below `2^56 + 32` (`BoundedEnv`), and nothing else changes but the
registers `workRegs` and the memory of the slots and of the products'
coefficients (`Keep`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv mulE addE subE)

theorem slot_idx {n : Nat} (h : n < 22) :
    Impl.X448.AArch64.slot n = Impl.X448.AArch64.slot (idx n).val := by
  simp only [idx, Nat.mod_eq_of_lt h]

theorem fop_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (op : FOp)
    (hv : fopValid op) :
    WP isa (Impl.X448.AArch64.Weak.code (toOp op)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = evalOp op (E s.mem base) := by
  cases op with
  | mul o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.AArch64.Weak.code, slot_idx h1, slot_idx h2, slot_idx h3]
    exact mulE hs hb _ _ _
  | sqr o a =>
    obtain ⟨h1, h2⟩ := hv
    simp only [toOp, Impl.X448.AArch64.Weak.code, slot_idx h1, slot_idx h2]
    exact mulE hs hb _ _ _
  | add o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.AArch64.Weak.code, slot_idx h1, slot_idx h2, slot_idx h3]
    exact addE hs hb _ _ _
  | sub o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.AArch64.Weak.code, slot_idx h1, slot_idx h2, slot_idx h3]
    exact subE hs hb _ _ _

theorem field_ok (ops : List FOp) (hv : ∀ op ∈ ops, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) (hb : BoundedEnv s.mem base) :
    WP isa (field ops) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = evalOps ops (E s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨VG.Proof.X448.AArch64.Keep.refl _ _, hb, rfl⟩
  | cons op ops ih =>
    change WP isa (.seq (Impl.X448.AArch64.Weak.code (toOp op)) (field ops)) s _
    rw [WP.seq_iff]
    refine WP.mono (fop_ok hs hb op (hv op List.mem_cons_self)) fun t ⟨tk, tb, te⟩ => ?_
    refine WP.mono (ih (fun o h => hv o (List.mem_cons_of_mem _ h)) (tk.scr hs) tb)
      fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]; rfl⟩

end VG.Proof.Ed448.AArch64
