import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit
import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase

/-!
# Ed25519's base-point multiplication on AArch64: the code without its immediates

Untrusted: everything here is checked by Lean. The constant-time analysis and
`keepsV` do not read the immediates of `movz` and `movk` (`Code.eraseImm`), and
without them the comb's selections from the 32 tables are the same code, table
0's (`combMultiply_eraseImm`, proven without evaluating them). The kernel,
evaluating the analysis of `scalarBaseEngine0` or the `keepsV` check of
`scalarBase0`, then builds no table's immediates, and builds and checks one
selection rather than 32: it caches the check of the same code from the same
state. These checks are the code's only evaluations (one each), so the code
has no literal (`materialize_code`), which would cost more to check than it
saves.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

/-- `combSelectFrom`, with every table's selection table 0's. -/
def combSelectFrom0 : List Nat → Prog isa
  | [] => .block []
  | j :: js => .seq (.block [.subImm .x .x9 .x19 j])
      (.ite (.zero .x .x9) (.block (combSelect 0)) (combSelectFrom0 js))

/-- `combStep`, with every table's selection table 0's. -/
def combStep0 : Prog isa :=
  .seq (.block combDigits) <|
  .seq (combSelectFrom0 (List.range 32)) <|
  .block (combNeg 4 5 6 772 ++ fieldCode addOddOps ++
    combNeg 13 14 15 768 ++ fieldCode addEvenOps ++
    [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 32])

/-- `combMultiply`, with every table's selection table 0's. -/
def combMultiply0 : Prog isa :=
  .seq (.block combInit) (.seq (.loop combStep0 (.nonzero .x .x8)) combFinish)

/-- `scalarBaseEngine`, with every table's selection table 0's. -/
def scalarBaseEngine0 : Prog isa := .seq scalarBasePrepare (.seq combMultiply0 pointEncode)

/-- `scalarBase`, with every table's selection table 0's. -/
def scalarBase0 : Prog isa :=
  .seq (.block (scalarSave ++ scalarBaseSetup)) (.seq scalarBaseEngine0 scalarBaseFinish)

/-- `selectCand` without its immediates. -/
def selectCandE (k w : Nat) : List Instr := (selectCand 0 k w).map Instr.eraseImm

theorem selectCand_eraseImm (v : Spec.X25519.Fe) (k w : Nat) :
    (selectCand v k w).map Instr.eraseImm = selectCandE k w := rfl

/-- `selectWord` without its immediates. -/
def selectWordE (one : Bool) (o e w : Nat) : List Instr :=
  (selectWord one [] o e w).map Instr.eraseImm

theorem selectWord_eraseImm (one : Bool) (vs : List Spec.X25519.Fe) (o e w : Nat) :
    (selectWord one vs o e w).map Instr.eraseImm = selectWordE one o e w := by
  simp only [selectWordE, selectWord, List.map_append, List.map_flatMap, selectCand_eraseImm]

theorem combSelect_eraseImm (j : Nat) :
    (combSelect j).map Instr.eraseImm = (combSelect 0).map Instr.eraseImm := by
  simp only [combSelect, selectField, List.map_append, List.map_flatMap, selectWord_eraseImm]

theorem combSelectFrom_eraseImm (js : List Nat) :
    Code.eraseImm (combSelectFrom js) = Code.eraseImm (combSelectFrom0 js) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [combSelectFrom, combSelectFrom0, Code.eraseImm, combSelect_eraseImm, ih]

theorem combMultiply_eraseImm : Code.eraseImm combMultiply = Code.eraseImm combMultiply0 := by
  simp only [combMultiply, combMultiply0, combStep, combStep0, Code.eraseImm,
    combSelectFrom_eraseImm]

theorem scalarBaseEngine_eraseImm :
    Code.eraseImm scalarBaseEngine = Code.eraseImm scalarBaseEngine0 := by
  simp only [scalarBaseEngine, scalarBaseEngine0, Code.eraseImm, combMultiply_eraseImm]

theorem scalarBase_eraseImm : Code.eraseImm scalarBase = Code.eraseImm scalarBase0 := by
  simp only [scalarBase, scalarBase0, Code.eraseImm, scalarBaseEngine_eraseImm]

end VG.Proof.Ed25519.AArch64
