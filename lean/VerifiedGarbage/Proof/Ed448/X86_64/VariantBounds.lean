module

public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
public import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Stack and register bounds shared by callers of every field backend. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

/-- No instruction of `c` writes `rsp` if its inlining is checked (`Code.InlineOk`), which checks
that of every instruction: the code's walk shared with its proof. -/
theorem nosp_of_inlineOk {c : Prog isa} (h : c.InlineOk = true) : NoSp c := by
  have h' : c.inline.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi; simp [Code.clobbers_rsp_of_inlineOk h i hi]
  rw [Code.allInstrs_inline, Code.allInstrs_eq] at h'
  intro i hi; simpa using List.all_eq_true.mp h' i hi

theorem scalarBaseFor_nosp (v : Impl.Ed448.X86_64.FieldVariant) : NoSp (scalarBaseFor v) := by
  cases v
  · exact nosp_of_inlineOk scalarBase_inlineOk
  · exact nosp_of_inlineOk scalarBaseAdx_inlineOk

theorem scalarBaseFor_depth (v : Impl.Ed448.X86_64.FieldVariant) : (scalarBaseFor v).depth ≤ 1 := by
  cases v <;> lit_decide

theorem verifyEquationFor_nosp (v : Impl.Ed448.X86_64.FieldVariant) : NoSp (verifyEquationFor v) := by
  cases v
  · exact nosp_of_inlineOk verifyEquation_inlineOk
  · exact nosp_of_inlineOk verifyEquationAdx_inlineOk

theorem verifyEquationFor_depth (v : Impl.Ed448.X86_64.FieldVariant) : (verifyEquationFor v).depth ≤ 1 := by
  cases v <;> lit_decide

end VG.Proof.Ed448.X86_64
