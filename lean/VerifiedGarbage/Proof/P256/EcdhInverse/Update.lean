import VerifiedGarbage.Impl.P256.EcdhInverse
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ObservedInputs
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Literal

namespace VG.Proof.P256.EcdhInverse.Update
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64.Forward VG.Proof.Mont VG.Proof.Mont.AArch64

def original : List Instr := .movz .x .x12 0 0 :: p256.invP.fgUpdate ++ p256.invP.abUpdate
def optimized := VG.Impl.P256.EcdhInverse.update

def observe (off : Nat) : Prop :=
 (2272≤off ∧ off<2352) ∨ (2352≤off ∧ off<2416)
instance (off : Nat) : Decidable (observe off) := inferInstanceAs
  (Decidable ((2272≤off ∧ off<2352) ∨ (2352≤off ∧ off<2416)))

materialize_value leftCode := original
materialize_value rightCode := optimized
certificate_value nodes := (buildPairFrom 8192 original optimized (matrixNodes 8192) (matrixEnv 8192)).getD ⟨.empty,.empty⟩

theorem valid : CertValid nodes := by decide +kernel

theorem inputs : Inputs nodes 8192 := by
  have h : ∀ i : Fin 1024,nodes.nodes.lookup (i.val+1)=some (.input (8*i.val)) := by decide +kernel
  intro off ha hb
  have ho : off=8*(off/8) := by omega
  simpa only [←ho] using h ⟨off/8,by omega⟩

theorem matrixInputs :
    nodes.nodes.lookup 1025=some (.input 8192) ∧ nodes.nodes.lookup 1026=some (.input 8200) ∧
    nodes.nodes.lookup 1027=some (.input 8208) ∧ nodes.nodes.lookup 1028=some (.input 8216) := by decide +kernel

noncomputable def left : Env Nat := (eval (certDom nodes) 8192 leftCode.lit (matrixEnv 8192)).getD (matrixEnv 8192)
noncomputable def right : Env Nat := (eval (certDom nodes) 8192 rightCode.lit (matrixEnv 8192)).getD (matrixEnv 8192)

private theorem some_getD {α : Type} {o : Option α} (d : α) (h : o.isSome=true) :
    o=some (o.getD d) := by cases o <;> simp_all

theorem evalLeft : eval (certDom nodes) 8192 original (matrixEnv 8192)=some left := by
  rw [leftCode.lit_eq]
  exact some_getD (matrixEnv 8192) (by decide +kernel)

theorem evalRight : eval (certDom nodes) 8192 optimized (matrixEnv 8192)=some right := by
  rw [rightCode.lit_eq]
  exact some_getD (matrixEnv 8192) (by decide +kernel)

theorem same : ∀ off,observe off → off%8=0 → off+8≤8192 → left.slot off=right.slot off := by
  have h : ∀ i : Fin 1024,observe (8*i.val) → left.slot (8*i.val)=right.slot (8*i.val) := by decide +kernel
  intro off ho ha hb
  have he : off=8*(off/8) := by omega
  simpa only [←he] using h ⟨off/8,by omega⟩ (by simpa only [←he] using ho)

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
  have h : leftCode.lit.all (fun i => decide (instrBound i≤8192))=true := by decide +kernel
  rw [leftCode.lit_eq]
  intro i hi
  exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)

 theorem rightBound : ∀ i∈optimized,instrBound i≤8192 := by
  have h : rightCode.lit.all (fun i => decide (instrBound i≤8192))=true := by decide +kernel
  rw [rightCode.lit_eq]
  intro i hi
  exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)

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

end VG.Proof.P256.EcdhInverse.Update
