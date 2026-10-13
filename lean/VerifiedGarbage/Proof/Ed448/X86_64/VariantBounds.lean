module

public import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit

/-! Stack and register bounds shared by callers of every field backend. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

theorem scalarBaseFor_nosp (v : Impl.Ed448.X86_64.FieldVariant) : NoSp (scalarBaseFor v) := by
  have h : ((instrs (scalarBaseFor v)).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; cases v <;> lit_decide
  intro i hi; simpa using List.all_eq_true.mp h i hi

theorem scalarBaseFor_depth (v : Impl.Ed448.X86_64.FieldVariant) : (scalarBaseFor v).depth ≤ 1 := by
  cases v <;> lit_decide

theorem verifyEquationFor_nosp (v : Impl.Ed448.X86_64.FieldVariant) : NoSp (verifyEquationFor v) := by
  have h : ((instrs (verifyEquationFor v)).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; cases v <;> lit_decide
  intro i hi; simpa using List.all_eq_true.mp h i hi

theorem verifyEquationFor_depth (v : Impl.Ed448.X86_64.FieldVariant) : (verifyEquationFor v).depth ≤ 1 := by
  cases v <;> lit_decide

end VG.Proof.Ed448.X86_64
