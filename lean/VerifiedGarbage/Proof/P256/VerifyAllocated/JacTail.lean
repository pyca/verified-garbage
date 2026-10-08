import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Impl.P256.VerifyAllocated
import VerifiedGarbage.Proof.P256.VerifyAllocated.Case
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Literal
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.P256.VerifyAllocated.JacTail
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

def original := VG.Impl.P256.VerifyAllocated.raw .jacTail
def optimized := VG.Impl.P256.VerifyAllocated.code .jacTail
materialize_value leftCode := original
materialize_value rightCode := optimized
forward_state bundle :=
  let ns := (buildPair 8192 original optimized).getD ⟨.empty,.empty⟩
  (ns, evalData (certDom ns) 8192 original initialEnv,
       evalData (certDom ns) 8192 optimized initialEnv)
noncomputable def nodes := bundle.1
noncomputable def leftData := bundle.2.1
noncomputable def rightData := bundle.2.2
theorem original_lit : original=leftCode.lit := leftCode.lit_eq
theorem optimized_lit : optimized=rightCode.lit := rightCode.lit_eq

theorem valid : CertValid nodes := by decide +kernel

theorem inputs : Inputs nodes 8192 := by
  have h : ∀ i : Fin 1024,nodes.nodes.lookup (i.val+1)=some (.input (8*i.val)) := by decide +kernel
  intro off ha hb
  have ho : off=8*(off/8) := by omega
  simpa only [←ho] using h ⟨off/8,by omega⟩

noncomputable def left : Env Nat := fromData initialEnv (leftData.getD (.empty, .empty, none))
noncomputable def right : Env Nat := fromData initialEnv (rightData.getD (.empty, .empty, none))

private theorem some_getD {α : Type} {o : Option α} (d : α) (h : o.isSome=true) :
    o=some (o.getD d) := by cases o <;> simp_all

theorem evalLeft : eval (certDom nodes) 8192 original initialEnv=some left := by
  rw [original_lit]
  exact eval_of_data (d := leftData.getD (.empty, .empty, none)) (by kernel_rfl)

theorem evalRight : eval (certDom nodes) 8192 optimized initialEnv=some right := by
  rw [optimized_lit]
  exact eval_of_data (d := rightData.getD (.empty, .empty, none)) (by kernel_rfl)

def observe := VG.Proof.P256.VerifyAllocated.observe .jacTail
instance (off : Nat) : Decidable (observe off) := by unfold observe; infer_instance

theorem same : ∀ off,observe off → off%8=0 → off+8≤8192 → left.slot off=right.slot off := by
  have h : ∀ i : Fin 1024,observe (8*i.val) → left.slot (8*i.val)=right.slot (8*i.val) := by decide +kernel
  intro off hv ha hb
  have ho : off=8*(off/8) := by omega
  have hh := h ⟨off/8,by omega⟩
  simpa only [←ho] using hh (by simpa only [←ho] using hv)

noncomputable def checked : CheckedObserved 8192 observe original optimized where
  nodes := nodes
  valid := valid
  initial := initialEnv
  left := left
  right := right
  evalLeft := evalLeft
  evalRight := evalRight
  same := same

noncomputable def caseProof : VG.Proof.P256.VerifyAllocated.Case .jacTail where
  checked := checked
  inputs := inputs
  initial := rfl
  leftBound := by
    have h : leftCode.lit.all (fun i => decide (instrBound i≤8192))=true := by decide +kernel
    rw [show VG.Impl.P256.VerifyAllocated.raw .jacTail=leftCode.lit from original_lit]
    intro i hi
    exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)
  rightBound := by
    have h : rightCode.lit.all (fun i => decide (instrBound i≤8192))=true := by decide +kernel
    rw [show VG.Impl.P256.VerifyAllocated.code .jacTail=rightCode.lit from optimized_lit]
    intro i hi
    exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)
  clob := by
    rw [show VG.Impl.P256.VerifyAllocated.code .jacTail=rightCode.lit from optimized_lit]
    decide +kernel
  writes := by
    rw [show VG.Impl.P256.VerifyAllocated.code .jacTail=rightCode.lit from optimized_lit]
    decide +kernel

end VG.Proof.P256.VerifyAllocated.JacTail
