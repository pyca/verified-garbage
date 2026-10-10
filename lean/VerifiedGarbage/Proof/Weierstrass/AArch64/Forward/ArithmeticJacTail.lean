import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

def original := Arithmetic.original .jacTail
def optimized := Arithmetic.optimized .jacTail
materialize_value leftCode := original
forward_state rightCode.lit := optimized
theorem rightCode.lit_eq : optimized=rightCode.lit := optimize_of_lit leftCode.lit_eq (by kernel_rfl)
theorem original_lit : original=leftCode.lit := leftCode.lit_eq
theorem optimized_lit : optimized=rightCode.lit := rightCode.lit_eq

theorem wf : wfK 8192 original (RegSet.empty,false)=true := by
  rw [original_lit]; decide +kernel

theorem leftBound : ∀ i∈original,instrBound i≤8192 := by
  rw [original_lit]; exact bound_of_listAllK (by decide +kernel)

private theorem rightOk : listAllK (instrOkK 8192 (RegSet.ofList (VG.Proof.Mont.AArch64.clob 4))
    [(0,8192)]) rightCode.lit=true := by decide +kernel

theorem rightBound : ∀ i∈optimized,instrBound i≤8192 := by
  rw [optimized_lit]; exact bound_of_instrOk rightOk

theorem clob : ∀ r∈optimized.flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob 4 := by
  rw [optimized_lit]; exact clob_of_instrOk rightOk

theorem checked : OptChecked 8192 original optimized :=
  ⟨rfl,wf,writes_of_bound leftBound,writes_of_bound rightBound⟩


theorem caseProof : Arithmetic.Case .jacTail where
  checked := checked
  leftBound := leftBound
  rightBound := rightBound
  clob := clob


theorem ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (VG.Impl.P256.VerifyArithmetic.program VG.Impl.P256.VerifyDouble.M
      (VG.Impl.P256.VerifyArithmetic.operations .jacTail)) := by
  have hs : VG.Impl.P256.VerifyArithmetic.selected VG.Impl.P256.VerifyDouble.M
      (VG.Impl.P256.VerifyArithmetic.operations .jacTail) :=
    ⟨rfl,List.mem_map.mpr ⟨.jacTail,by simp [VG.Impl.P256.VerifyArithmetic.kinds],rfl⟩⟩
  rw [VG.Impl.P256.VerifyArithmetic.program,ite_eq_left hs]
  change ConstantTime isa _ _ (.block optimized)
  rw [optimized_lit]
  exact VG.Taint.constantTime (A:=taint) (hc:=.block (List.replicate 5 (Taint.ofRegs [.x0])))
    (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by decide +kernel)

end VG.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
