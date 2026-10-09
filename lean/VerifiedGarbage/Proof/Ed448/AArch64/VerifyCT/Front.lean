import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Erase
import VerifiedGarbage.Proof.X448.AArch64.Base.Erase

/-!
# Ed448 verification's equation on AArch64: constant time of the entry, the table and `[S]B`

Untrusted: everything here is checked by Lean. The analysis of each phase of
`verifyEquation` (with the address of the comb's tables public, `taintS`) is
evaluated in a declaration of its own (here and in `VerifyCT/Windows.lean`),
which the modules check in
parallel, and composed by `seq_ok`: between the phases only the working
space's pointer, `x3`, is public. The field operations, erased
(`Proof/X448/AArch64/Fast/Erase.lean`), are analysed as pieces of their
blocks (`Split`): once each, not once for every slot they work on.
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

theorem front_ct : ∃ h, ((taintS [Impl.X448.AArch64.Base.combSym]).check
    (Taint.ofRegs [.x0, .x1, .x2, .x3]) wfront h).map
    ((taintS [Impl.X448.AArch64.Base.combSym]).le (Taint.ofRegs [.x3])) = some true := by
  apply exists_map_le_of_eraseT
  simp only [Code.eraseT, wfront, bitsAt, vdecodeA, decode, root, ops_eraseT, sqn_eraseT, List.map_append,
    eqSlots_eraseT]
  refine ⟨?h, ?g⟩
  case g => taint_decide

open VG.Impl.X448.AArch64 (slot) in
/-- The body of the table's loop, erased, in pieces. -/
def tabPieces : List (List Instr) :=
  (Impl.X448.AArch64.Base.addOps (slot 0) (slot 1) (slot 2) (slot 3) (slot 4) (slot 5)).map opErased ++
    [(tabStore ++ ([.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 16] : List Instr)).map Instr.eraseT]

theorem table_ct : ∃ h, ((taintS [Impl.X448.AArch64.Base.combSym]).check (Taint.ofRegs [.x3]) table h).map
    ((taintS [Impl.X448.AArch64.Base.combSym]).le (Taint.ofRegs [.x3])) = some true := by
  apply exists_map_le_of_eraseT
  refine Split.exists_map_le (c' := ?c') ?s ⟨?h, ?g⟩
  case s =>
    have e : tabBody.map Instr.eraseT = tabPieces.flatten := by
      simp only [tabBody, tabPieces, List.map_append, codeOf_eraseT, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.append_assoc]
    simp only [Code.eraseT, table, e]
    exact .seq (.refl _) (.loop _ (.pieces _))
  case g => taint_decide

theorem sBase_ct : ∃ h, ((taintS [Impl.X448.AArch64.Base.combSym]).check (Taint.ofRegs [.x3]) sBase h).map
    ((taintS [Impl.X448.AArch64.Base.combSym]).le (Taint.ofRegs [.x3])) = some true := by
  apply exists_map_le_of_eraseT
  refine Split.exists_map_le (c' := ?c') ?s ⟨?h, ?g⟩
  case s =>
    simp only [sBase, Code.eraseT]
    exact .seq (.refl _) (.seq (.loop _ (stepN_split 57)) combine_split)
  case g => taint_decide

end VG.Proof.Ed448.AArch64
