import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

def original := Arithmetic.original .mixedTail
def optimized := Arithmetic.optimized .mixedTail
materialize_value leftCode := original
materialize_value rightCode := optimized
forward_state bundle :=
  let ns := (buildPair 8192 original optimized).getD ⟨.empty,.empty⟩
  (ns,(evalData (certDom ns) 8192 original initialEnv).getD (.empty,.empty,none),
    (evalData (certDom ns) 8192 optimized initialEnv).getD (.empty,.empty,none))
noncomputable def nodes := bundle.1
theorem original_lit : original=leftCode.lit := leftCode.lit_eq
theorem optimized_lit : optimized=rightCode.lit := rightCode.lit_eq

theorem valid : CertValid nodes := valid_of_validK (by decide +kernel)

theorem inputs : Inputs nodes 8192 := inputs_of_allBelow (by decide +kernel)

noncomputable def left : Env Nat := fromData initialEnv bundle.2.1
noncomputable def right : Env Nat := fromData initialEnv bundle.2.2

theorem evalLeft : eval (certDom nodes) 8192 original initialEnv=some left := by
  rw [original_lit]
  exact eval_of_dataK (by kernel_rfl)

theorem evalRight : eval (certDom nodes) 8192 optimized initialEnv=some right := by
  rw [optimized_lit]
  exact eval_of_dataK (by kernel_rfl)

theorem same : ∀ off,off%8=0 → off+8≤8192 → left.slot off=right.slot off :=
  fun off _ _ => same_of_sameK (fun _ => True) (by decide +kernel) off trivial

theorem leftBound : ∀ i∈original,instrBound i≤8192 := by
  rw [original_lit]; exact bound_of_listAllK (by decide +kernel)

private theorem rightOk : listAllK (instrOkK 8192 (RegSet.ofList (VG.Proof.Mont.AArch64.clob 4))
    [(0,8192)]) rightCode.lit=true := by decide +kernel

theorem rightBound : ∀ i∈optimized,instrBound i≤8192 := by
  rw [optimized_lit]; exact bound_of_instrOk rightOk

theorem clob : ∀ r∈optimized.flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob 4 := by
  rw [optimized_lit]; exact clob_of_instrOk rightOk

noncomputable def checked : Checked 8192 original optimized where
  nodes := nodes
  valid := valid
  inputs := inputs
  left := left
  right := right
  evalLeft := evalLeft
  evalRight := evalRight
  same := same
  boundLeft := writes_of_bound leftBound
  boundRight := writes_of_bound rightBound


noncomputable def caseProof : Arithmetic.Case .mixedTail where
  checked := checked
  leftBound := leftBound
  rightBound := rightBound
  clob := clob


theorem ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (VG.Impl.P256.VerifyArithmetic.program VG.Impl.P256.VerifyDouble.M
      (VG.Impl.P256.VerifyArithmetic.operations .mixedTail)) := by
  have hs : VG.Impl.P256.VerifyArithmetic.selected VG.Impl.P256.VerifyDouble.M
      (VG.Impl.P256.VerifyArithmetic.operations .mixedTail) :=
    ⟨rfl,List.mem_map.mpr ⟨.mixedTail,by simp [VG.Impl.P256.VerifyArithmetic.kinds],rfl⟩⟩
  rw [VG.Impl.P256.VerifyArithmetic.program,ite_eq_left hs]
  change ConstantTime isa _ _ (.block optimized)
  rw [optimized_lit]
  exact VG.Taint.constantTime (A:=taint) (hc:=.block (List.replicate 5 (Taint.ofRegs [.x0])))
    (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by decide +kernel)

end VG.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
