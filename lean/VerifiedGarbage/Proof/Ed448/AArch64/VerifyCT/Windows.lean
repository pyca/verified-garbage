import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Erase

/-!
# Ed448 verification's equation on AArch64: constant time of the windows and the comparison

Untrusted: everything here is checked by Lean. As `VerifyCT/Front.lean`, for
the last two phases: the windows over the challenge, and the comparison with
the result. The field operations, erased (`Proof/X448/AArch64/Fast/Erase.lean`),
are analysed as pieces of their blocks (`Split`): once each, not once for
every slot they work on.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Impl.X448.AArch64.Fast (codeOf)

/-- Four doublings' body, erased, in pieces. -/
def dblPieces : List (List Instr) :=
  (dblOps (slot 3) (slot 4) (slot 5)).map opErased ++ [[Instr.subImm .x .x1 .x1 1].map Instr.eraseT]

theorem dblBody_eraseT :
    (codeOf (dblOps (slot 3) (slot 4) (slot 5)) ++ [Instr.subImm .x .x1 .x1 1]).map Instr.eraseT =
      dblPieces.flatten := by
  simp only [dblPieces, List.map_append, codeOf_eraseT, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil]

/-- A window's addition of the selected entry, erased, in pieces. -/
def addPieces (sh : Nat) : List (List Instr) :=
  [(digitOf sh).map Instr.eraseT, selectEntry.map Instr.eraseT] ++
    (Impl.X448.AArch64.Base.addOps (slot 3) (slot 4) (slot 5) (slot 6) (slot 7) (slot 8)).map opErased

theorem addBlock_eraseT (sh : Nat) :
    (digitOf sh ++ selectEntry ++
      codeOf (Impl.X448.AArch64.Base.addOps (slot 3) (slot 4) (slot 5) (slot 6) (slot 7) (slot 8))).map
        Instr.eraseT = (addPieces sh).flatten := by
  simp only [addPieces, List.map_append, codeOf_eraseT, List.flatten_cons, List.cons_append, List.nil_append,
    List.append_assoc]

theorem kWindows_ct : ∃ h, ((taintS [Impl.X448.AArch64.Base.combSym]).check (Taint.ofRegs [.x3]) kWindows h).map
    ((taintS [Impl.X448.AArch64.Base.combSym]).le (Taint.ofRegs [.x3])) = some true := by
  apply exists_map_le_of_eraseT
  refine Split.exists_map_le (c' := ?c') ?s ⟨?h, ?g⟩
  case s =>
    simp only [Code.eraseT, kWindows, kByte, window, dbl4Loop, dblBody_eraseT, addBlock_eraseT]
    exact .seq (.refl _) (.loop _ (.seq (.refl _) (.seq (.seq (.seq (.refl _) (.loop _ (.pieces _)))
      (.pieces _)) (.seq (.seq (.refl _) (.loop _ (.pieces _))) (.pieces _)))))
  case g => taint_decide

/-- The comparison's code, erased, in pieces. -/
def tailPieces : List (List Instr) :=
  (Impl.X448.AArch64.Base.addOps (slot 0) (slot 1) (slot 2) (slot 3) (slot 4) (slot 5)).map opErased ++
  [(Impl.Curve448.AArch64.copy (slot 6) RX ++ Impl.Curve448.AArch64.copy (slot 7) RY ++
    Impl.X448.AArch64.Base.constSlot (slot 8) 1).map Instr.eraseT] ++
  (dblOps (slot 0) (slot 1) (slot 2) ++ dblOps (slot 0) (slot 1) (slot 2) ++
    dblOps (slot 6) (slot 7) (slot 8) ++ dblOps (slot 6) (slot 7) (slot 8) ++
    ([.mul (slot 12) (slot 0) (slot 8), .mul (slot 13) (slot 6) (slot 2),
      .mul (slot 14) (slot 1) (slot 8), .mul (slot 15) (slot 7) (slot 2)] :
        List Impl.X448.AArch64.Fast.Op)).map opErased ++
  [eqSlotsE, eqSlotsE,
    (([Instr.addImm .x .x5 .x20 0] : List Instr) ++ isZero ++ [Instr.addImm .x .x0 .x5 0, Impl.X448.AArch64.ld .x19 0,
      Impl.X448.AArch64.ld .x20 8] ++ Impl.X448.AArch64.Fast.restore ++
      Impl.X448.AArch64.Fast.vrestore).map Instr.eraseT]

theorem tail_eraseT : (wcross ++ wfinish).map Instr.eraseT = tailPieces.flatten := by
  simp only [tailPieces, wcross, wfinish, List.map_append, codeOf_eraseT, eqSlots_eraseT, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

theorem tail_ct :
    ∃ h, ((taintS [Impl.X448.AArch64.Base.combSym]).check (Taint.ofRegs [.x3])
      (.block (wcross ++ wfinish)) h).isSome = true := by
  apply exists_isSome_of_eraseT
  rw [Code.eraseT, tail_eraseT]
  refine Split.exists_isSome (Split.pieces _) ⟨?h, ?g⟩
  case g => taint_decide

end VG.Proof.Ed448.AArch64
