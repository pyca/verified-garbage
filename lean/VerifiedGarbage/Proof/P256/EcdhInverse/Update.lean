module

public import VerifiedGarbage.Impl.P256.EcdhInverse
meta import VerifiedGarbage.Impl.P256.EcdhInverse
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ObservedInputs
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Observed
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ObservedInputs
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import Mathlib.Logic.Function.Basic
meta import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Impl.Ecdh.P256.AArch64
meta import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Observed
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.JacMul
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.Weierstrass.Mul

@[expose] public section

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

end VG.Proof.P256.EcdhInverse.Update
