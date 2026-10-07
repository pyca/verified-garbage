import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Literal
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

def original := Arithmetic.original .jacHead
def optimized := Arithmetic.optimized .jacHead
materialize_value leftCode := original
materialize_value rightCode := optimized
certificate_value nodes := (buildPair 8192 original optimized).getD ⟨.empty,.empty⟩
theorem original_lit : original=leftCode.lit := leftCode.lit_eq
theorem optimized_lit : optimized=rightCode.lit := rightCode.lit_eq

theorem valid : CertValid nodes := by decide +kernel

theorem inputs : Inputs nodes 8192 := by
  have h : ∀ i : Fin 1024,nodes.nodes.lookup (i.val+1)=some (.input (8*i.val)) := by decide +kernel
  intro off ha hb
  have ho : off=8*(off/8) := by omega
  simpa only [←ho] using h ⟨off/8,by omega⟩

noncomputable def left : Env Nat := (eval (certDom nodes) 8192 leftCode.lit initialEnv).getD initialEnv
noncomputable def right : Env Nat := (eval (certDom nodes) 8192 rightCode.lit initialEnv).getD initialEnv

private theorem some_getD {α : Type} {o : Option α} (d : α) (h : o.isSome=true) :
    o=some (o.getD d) := by cases o <;> simp_all

theorem evalLeft : eval (certDom nodes) 8192 original initialEnv=some left := by
  rw [original_lit]
  exact some_getD initialEnv (by decide +kernel)

theorem evalRight : eval (certDom nodes) 8192 optimized initialEnv=some right := by
  rw [optimized_lit]
  exact some_getD initialEnv (by decide +kernel)

theorem same : ∀ off,off%8=0 → off+8≤8192 → left.slot off=right.slot off := by
  have h : ∀ i : Fin 1024,left.slot (8*i.val)=right.slot (8*i.val) := by decide +kernel
  intro off ha hb
  have ho : off=8*(off/8) := by omega
  simpa only [←ho] using h ⟨off/8,by omega⟩

noncomputable def checked : Checked 8192 original optimized where
  nodes := nodes
  valid := valid
  inputs := inputs
  left := left
  right := right
  evalLeft := evalLeft
  evalRight := evalRight
  same := same
  boundLeft := by rw [original_lit]; decide +kernel
  boundRight := by rw [optimized_lit]; decide +kernel


noncomputable def caseProof : Arithmetic.Case .jacHead where
  checked := checked
  leftBound := by
    have h : leftCode.lit.all (fun i => decide (instrBound i≤8192))=true := by decide +kernel
    rw [show Arithmetic.original _=leftCode.lit from original_lit]
    intro i hi
    exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)
  rightBound := by
    have h : rightCode.lit.all (fun i => decide (instrBound i≤8192))=true := by decide +kernel
    rw [show Arithmetic.optimized _=rightCode.lit from optimized_lit]
    intro i hi
    exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)
  clob := by
    have h : (rightCode.lit.flatMap instrClob).all
        (fun r => decide (r∈VG.Proof.Mont.AArch64.clob 4))=true := by decide +kernel
    rw [show Arithmetic.optimized .jacHead=rightCode.lit from optimized_lit]
    intro r hr
    exact of_decide_eq_true ((List.all_eq_true.mp h) r hr)


theorem ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (VG.Impl.P256.VerifyArithmetic.program VG.Impl.P256.VerifyDouble.M
      (VG.Impl.P256.VerifyArithmetic.operations .jacHead)) := by
  have hs : VG.Impl.P256.VerifyArithmetic.selected VG.Impl.P256.VerifyDouble.M
      (VG.Impl.P256.VerifyArithmetic.operations .jacHead) :=
    ⟨rfl,List.mem_map.mpr ⟨.jacHead,by simp [VG.Impl.P256.VerifyArithmetic.kinds],rfl⟩⟩
  rw [VG.Impl.P256.VerifyArithmetic.program,ite_eq_left hs]
  change ConstantTime isa _ _ (.block optimized)
  rw [optimized_lit]
  exact VG.Taint.constantTime (A:=taint) (hc:=.block (List.replicate 5 (Taint.ofRegs [.x0])))
    (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by decide +kernel)

end VG.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
