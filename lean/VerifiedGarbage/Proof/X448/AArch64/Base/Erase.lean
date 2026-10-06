import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Impl.X448.AArch64.Base

/-!
# X448 of the base point on AArch64: the code without its immediates

Untrusted: everything here is checked by Lean. The constant-time analysis does
not read the immediates of `movz` and `movk` (`Code.eraseImm`), and without
them the selections from the tables are the same code, table 0's
(`x448Base_eraseImm`, proven without evaluating them). The kernel, evaluating
the analysis of `x448BaseErased` (`x448Base_ct`), then builds no table's
immediates, and builds and analyses one selection rather than one per table: it caches
the analysis of the same code from the same taint. The analysis is the code's
only evaluation, so the code has no literal (`materialize_code`), which would
cost more to check than it saves.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64.Base
open VG.Impl.X448.AArch64 (BITS)

/-- `selectFrom`, with every table's selection table 0's. -/
def selectFrom0 : List Nat → Prog isa
  | [] => .block []
  | j :: js => .seq (.block [.subImm .x .x9 .x19 j])
      (.ite (.zero .x .x9) (.block (select 0)) (selectFrom0 js))

/-- `stepN n`, with every table's selection table 0's. -/
def stepN0 (n : Nat) : Prog isa :=
  .seq (.block digits) <|
  .seq (selectFrom0 (List.range n)) <|
  .block (negate OX (BITS + 4) (t 0) ++ addAffine AX AY AZ OX OY ++
    negate EX BITS (t 0) ++ addAffine BX BY BZ EX EY ++
    [.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 n])

/-- `x448Base`, with every table's selection table 0's. -/
def x448Base0 : Prog isa :=
  .seq setup <| .seq (.loop (stepN0 56) (.nonzero .x .x9)) <| .seq combine finish

/-- `x448Base` without its immediates. -/
def x448BaseErased : Prog isa := Code.eraseImm x448Base0

/-- `const64 d v` without its immediates. -/
def const64E (d : Reg) : List Instr := (const64 d 0).map Instr.eraseImm

theorem const64_eraseImm (d : Reg) (v : BitVec 64) :
    (const64 d v).map Instr.eraseImm = const64E d := rfl

/-- `selectWord` without its immediates. -/
def selectWordE (one : Bool) (o e w : Nat) : List Instr :=
  (selectWord one [] o e w).map Instr.eraseImm

theorem selectWord_eraseImm (one : Bool) (vs : List Spec.X448.Fe) (o e w : Nat) :
    (selectWord one vs o e w).map Instr.eraseImm = selectWordE one o e w := by
  simp only [selectWordE, selectWord, List.map_append, List.map_flatMap, const64_eraseImm]

theorem select_eraseImm (j : Nat) :
    (select j).map Instr.eraseImm = (select 0).map Instr.eraseImm := by
  simp only [select, List.map_append, List.map_flatMap, selectWord_eraseImm]

theorem selectFrom_eraseImm (js : List Nat) :
    Code.eraseImm (selectFrom js) = Code.eraseImm (selectFrom0 js) := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [selectFrom, selectFrom0, Code.eraseImm, select_eraseImm, ih]

theorem stepN_eraseImm (n : Nat) : Code.eraseImm (stepN n) = Code.eraseImm (stepN0 n) := by
  simp only [stepN, stepN0, Code.eraseImm, selectFrom_eraseImm]

theorem x448Base_eraseImm : Code.eraseImm x448Base = x448BaseErased := by
  simp only [x448BaseErased, x448Base, x448Base0, step, Code.eraseImm, stepN_eraseImm]

end VG.Proof.X448.AArch64.Base
