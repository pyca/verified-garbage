import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ObservedInputs
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel

namespace VG.Proof.Weierstrass.AArch64.Forward.InvAllocated
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64.Forward VG.Proof.Mont VG.Proof.Mont.AArch64

def original : List Instr := .movz .x .x12 0 0 :: p256.invN.fgUpdate ++ p256.invN.abUpdate
def optimized := VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.inverseUpdate

def observe (off : Nat) : Prop := off<7104 ∨ 7680≤off
instance (off : Nat) : Decidable (observe off) := inferInstanceAs (Decidable (off<7104 ∨ 7680≤off))

materialize_value leftCode := original
materialize_value rightCode := optimized
forward_state bundle :=
  let ns := (buildPairFrom 8192 original optimized (matrixNodes 8192) (matrixEnv 8192)).getD ⟨.empty,.empty⟩
  (ns,(evalData (certDom ns) 8192 original (matrixEnv 8192)).getD (.empty,.empty,none),
    (evalData (certDom ns) 8192 optimized (matrixEnv 8192)).getD (.empty,.empty,none))
noncomputable def nodes := bundle.1

theorem valid : CertValid nodes := valid_of_validK (by decide +kernel)

theorem inputs : Inputs nodes 8192 := inputs_of_allBelow (by decide +kernel)

theorem matrixInputs :
    nodes.nodes.lookup 1025=some (.input 8192) ∧ nodes.nodes.lookup 1026=some (.input 8200) ∧
    nodes.nodes.lookup 1027=some (.input 8208) ∧ nodes.nodes.lookup 1028=some (.input 8216) := by decide +kernel

noncomputable def left : Env Nat := fromData (matrixEnv 8192) bundle.2.1
noncomputable def right : Env Nat := fromData (matrixEnv 8192) bundle.2.2

theorem evalLeft : eval (certDom nodes) 8192 original (matrixEnv 8192)=some left := by
  rw [leftCode.lit_eq]
  exact eval_of_dataK (by kernel_rfl)

theorem evalRight : eval (certDom nodes) 8192 optimized (matrixEnv 8192)=some right := by
  rw [rightCode.lit_eq]
  exact eval_of_dataK (by kernel_rfl)

theorem same : ∀ off,observe off → off%8=0 → off+8≤8192 → left.slot off=right.slot off :=
  fun off hv _ _ => same_of_sameK observe (by decide +kernel) off hv

noncomputable def checked : CheckedObserved 8192 observe original optimized where
  nodes := nodes
  valid := valid
  initial := matrixEnv 8192
  left := left
  right := right
  evalLeft := evalLeft
  evalRight := evalRight
  same := same

theorem initial_rel (s : State) (base : Addr) :
    Rel (nodeVal nodes (matrixInput 8192 s base)) base 8192 (matrixEnv 8192) s :=
  matrix_initial_rel inputs matrixInputs.1 matrixInputs.2.1 matrixInputs.2.2.1 matrixInputs.2.2.2 s base

 theorem leftBound : ∀ i∈original,instrBound i≤8192 := by
  rw [leftCode.lit_eq]; exact bound_of_listAllK (by decide +kernel)

 theorem rightBound : ∀ i∈optimized,instrBound i≤8192 := by
  rw [rightCode.lit_eq]; exact bound_of_listAllK (by decide +kernel)

 theorem keepsDeltaCounter : ∀ r∈optimized.flatMap instrClob,r≠.x1 ∧ r≠.x19 := by
  rw [rightCode.lit_eq]
  decide +kernel

 theorem refine {s : State} {base : Addr} {cap : Nat} (hs : Scr s base cap) (hcap : 8192≤cap)
    {Q : State → Prop} (hq : WP isa (.block original) s Q) :
    WP isa (.block optimized) s fun t => ∃ u,Q u ∧
      (∀ off,observe off → off%8=0 → off+8≤8192 →
        word t.mem base off=word u.mem base off) ∧
      VG.Proof.Mont.AArch64.KeepRegs (optimized.flatMap instrClob) s t ∧
      VG.Proof.Weierstrass.Unch base (optimized.flatMap instrWrites) s.mem t.mem :=
  checked.refine (matrixInput 8192 s base) (by decide) hs (initial_rel s base)
    (fun i hi => Nat.le_trans (leftBound i hi) hcap) (fun i hi => Nat.le_trans (rightBound i hi) hcap) hq

end VG.Proof.Weierstrass.AArch64.Forward.InvAllocated
