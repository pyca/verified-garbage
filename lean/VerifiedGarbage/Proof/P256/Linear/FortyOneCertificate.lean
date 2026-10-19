module

public import VerifiedGarbage.Proof.P256.Linear.FortyOneReference
meta import VerifiedGarbage.Proof.P256.Linear.FortyOneReference
public import VerifiedGarbage.Impl.P256.Linear
meta import VerifiedGarbage.Impl.P256.Linear
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Checked
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Checked
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.NatPairs
import VerifiedGarbage.Spec.Weierstrass.Point
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Impl.NatPairs
meta import VerifiedGarbage.Spec.Weierstrass.Point
import Mathlib.Logic.Function.Basic
meta import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Impl.P256.VerifyArithmetic
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Arithmetic
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
import VerifiedGarbage.Proof.P256.Linear.FortyOneValue
import VerifiedGarbage.Proof.P256.Linear.WeakCore
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Impl.P256.VerifyArithmetic
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Arithmetic
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
meta import VerifiedGarbage.Proof.P256.Linear.FortyOneValue
meta import VerifiedGarbage.Proof.P256.Linear.WeakCore
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.JacMul
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.Weierstrass.Mul

@[expose] public section

namespace VG.Proof.P256.Linear.FortyOneCertificate
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

def original := FortyOne.reference 512 928 960
def optimized := VG.Impl.P256.Linear.linear41 512 928 960
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

theorem rightBound : ∀ i∈optimized,instrBound i≤8192 := by
  rw [optimized_lit]; exact bound_of_listAllK (by decide +kernel)

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

end VG.Proof.P256.Linear.FortyOneCertificate
