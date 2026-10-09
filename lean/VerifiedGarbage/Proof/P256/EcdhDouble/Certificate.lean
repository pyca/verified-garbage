import VerifiedGarbage.Impl.P256.EcdhDouble
import VerifiedGarbage.Proof.P256.VerifyAllocated.Case
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.P256.EcdhDouble.Certificate
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

def original := VG.Impl.P256.EcdhDouble.raw
def optimized := VG.Impl.P256.EcdhDouble.code
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

def observe := VG.Proof.P256.VerifyAllocated.observe .doubleRR
instance (off : Nat) : Decidable (observe off) := by unfold observe; infer_instance

theorem same : ∀ off,observe off → off%8=0 → off+8≤8192 → left.slot off=right.slot off :=
  fun off hv _ _ => same_of_sameK observe (by decide +kernel) off hv

theorem leftBound : ∀ i∈original,instrBound i≤8192 := by
  rw [original_lit]; exact bound_of_listAllK (by decide +kernel)

private theorem rightOk : listAllK (instrOkK 8192 (RegSet.ofList (VG.Proof.Weierstrass.AArch64.allocatedRegs))
    VG.Proof.P256.VerifyAllocated.work) rightCode.lit=true := by decide +kernel

theorem rightBound : ∀ i∈optimized,instrBound i≤8192 := by
  rw [optimized_lit]; exact bound_of_instrOk rightOk

theorem clob : ∀ r∈optimized.flatMap instrClob,r∈VG.Proof.Weierstrass.AArch64.allocatedRegs := by
  rw [optimized_lit]; exact clob_of_instrOk rightOk

theorem writes : ∀ w∈optimized.flatMap instrWrites,
    ∃ w'∈VG.Proof.P256.VerifyAllocated.work,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  rw [optimized_lit]; exact cover_of_instrOk rightOk

noncomputable def checked : CheckedObserved 8192 observe original optimized where
  nodes := nodes
  valid := valid
  initial := initialEnv
  left := left
  right := right
  evalLeft := evalLeft
  evalRight := evalRight
  same := same

open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass.AArch64

theorem refine {base : Addr} {s : State} (hs : Scr s base 8192) {Q : State → Prop}
    (hq : WP isa (.block original) s Q) :
    WP isa Impl.P256.EcdhDouble.program s fun t => ∃ u,Q u ∧
      (∀ off,observe off → off%8=0 → off+8≤8192 →
        word t.mem base off=word u.mem base off) ∧
      AllocatedFrame allocatedRegs base VerifyAllocated.work s t := by
  exact WP.mono (checked.refine (word s.mem base) (by decide) hs (initial_rel inputs s base)
    leftBound rightBound hq) fun _ ⟨u,hu,hw,hk,hm⟩ => ⟨u,hu,hw,hk.mono clob,hm.cover writes⟩

theorem ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    Impl.P256.EcdhDouble.program := by
  change ConstantTime isa _ _ (.block optimized)
  rw [optimized_lit]
  exact VG.Taint.constantTime (A:=taint) (hc:=.block (List.replicate 5 (Taint.ofRegs [.x0])))
    (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by decide +kernel)

end VG.Proof.P256.EcdhDouble.Certificate
