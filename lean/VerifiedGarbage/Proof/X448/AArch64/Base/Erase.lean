import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase

/-!
# X448 of the base point on AArch64: the comb's code, erased

Untrusted: everything here is checked by Lean. The comb's step
(`Impl/X448/AArch64/Base.lean`), without what the analysis does not read, as
pieces that are the same code whatever the slots (the negations, the additions
of affine points): the constant-time check of `vg_ed448_r56_comb_base`, whose
loop it is, analyses each once (`Split`).
-/

namespace VG.AArch64

open VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Impl.X448.AArch64.Fast (codeOf weave)

/-- The conditional swap of two slots, erased. -/
def cswapE : List Instr := (Impl.Curve448.AArch64.cswap 0 0).map Instr.eraseT

theorem cswap_eraseT (x y : Nat) : (Impl.Curve448.AArch64.cswap x y).map Instr.eraseT = cswapE := by
  kernel_rfl

/-- A negation's code under its digit's sign, erased, in pieces. -/
def negPieces : List (List Instr) :=
  [subE, ([.lsl .x .x6 .x19 3, .add .x .x6 .x3 .x6, .ldrb .x6 .x6 0, .subImm .x .x6 .x6 1] : List Instr).map
    Instr.eraseT, cswapE]

theorem negate_eraseT (ox o w : Nat) : (negate ox o w).map Instr.eraseT = negPieces.flatten := by
  simp only [negate, negPieces, List.map_append, codeOf_eraseT, cswap_eraseT, List.map_cons, List.map_nil,
    opErased, List.flatten_cons, List.flatten_nil, List.append_nil, Instr.eraseT, List.append_assoc]

/-- The addition of an affine point, erased, in pieces: the same code whatever the slots. -/
def addAffinePieces : List (List Instr) :=
  [weave sqrE mul2E, weave (mulE ++ smallE ++ subE ++ smallE) mul2E, addSubE, addSubE, weave mulE mul2E,
    weave copyE mul2E]

theorem addAffine_eraseT (x1 y1 z1 x2 y2 : Nat) :
    (addAffine x1 y1 z1 x2 y2).map Instr.eraseT = addAffinePieces.flatten := by
  simp only [addAffine, addAffinePieces, List.map_append, weave_map, codeOf_eraseT, mul2_eraseT,
    List.map_cons, List.map_nil, opErased, t, slot, ZERO, Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff,
    ↓reduceIte, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

/-- The block of a step that negates the entries and adds them, erased, in pieces. -/
def stepPieces : List (List Instr) :=
  negPieces ++ addAffinePieces ++ negPieces ++ addAffinePieces ++
    [([.addImm .x .x19 .x19 1, .sub .x .x9 .x19 .x30] : List Instr).map Instr.eraseT]

theorem stepR_eraseT : Code.eraseT stepR =
    .seq (.block (digits.map Instr.eraseT)) (.seq (.block (select.map Instr.eraseT))
      (.block stepPieces.flatten)) := by
  simp only [stepR, Code.eraseT, List.map_append, negate_eraseT, addAffine_eraseT, stepPieces,
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc,
    List.map_cons, List.map_nil, Instr.eraseT]

theorem stepR_split : Split (Code.eraseT stepR) (.seq (.block (digits.map Instr.eraseT))
    (.seq (.block (select.map Instr.eraseT)) (piecesProg stepPieces))) := by
  rw [stepR_eraseT]
  exact .seq (.refl _) (.seq (.refl _) (.pieces _))

end VG.AArch64
