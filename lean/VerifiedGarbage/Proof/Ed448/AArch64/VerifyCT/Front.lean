import VerifiedGarbage.Proof.Ed448.AArch64.VerifyErase
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# Ed448 verification's equation on AArch64: constant time of the entry, the table and `[S]B`

Untrusted: everything here is checked by Lean. The analysis of each phase of
`verifyEquationErased` (`VerifyErase.lean`) is evaluated in a declaration of
its own (here and in `VerifyCT/Windows.lean`), which the modules check in
parallel, and composed by `seq_ok`: between the phases only the working
space's pointer, `x3`, is public.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

/-- The analysis of `c₁; c₂` from those of `c₁` (ending with at least `mid` public) and `c₂`
(from `mid`). -/
theorem seq_ok {M : ISA} {A : VG.Taint M} {τ mid : A.T} {c₁ c₂ : Prog M} {h₁ h₂ : VG.Taint.Hint A.T}
    (e₁ : (A.check τ c₁ h₁).map (A.le mid) = some true) (e₂ : (A.check mid c₂ h₂).isSome = true) :
    (A.check τ (.seq c₁ c₂) (.seq mid h₁ h₂)).isSome = true := by
  cases hc : A.check τ c₁ h₁ with
  | none => rw [hc] at e₁; cases e₁
  | some τ' =>
    rw [hc, Option.map_some, Option.some.injEq] at e₁
    simp only [VG.Taint.check, hc, Option.bind_some, e₁, ite_true, e₂]

theorem front_ct : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (Code.eraseImm wfront) h).map
    (taint.le (Taint.ofRegs [.x3])) = some true := by
  refine ⟨?h, ?g⟩
  case g => taint_decide

theorem table_ct : ∃ h, (taint.check (Taint.ofRegs [.x3]) (Code.eraseImm table) h).map
    (taint.le (Taint.ofRegs [.x3])) = some true := by
  refine ⟨?h, ?g⟩
  case g => taint_decide

theorem sBase_ct : ∃ h, (taint.check (Taint.ofRegs [.x3]) (Code.eraseImm sBase0) h).map
    (taint.le (Taint.ofRegs [.x3])) = some true := by
  refine ⟨?h, ?g⟩
  case g => taint_decide

end VG.Proof.Ed448.AArch64
