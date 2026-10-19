module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Selected
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Selected
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeK
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeK
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.Weierstrass.Mul
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
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.Comb
meta import VerifiedGarbage.Proof.Weierstrass.JacMul
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.Weierstrass.Mul

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward.P256Bounds
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.P256.VerifyDouble
open VG.Proof.Weierstrass.AArch64.Forward

materialize_value leftRD := Fixed.original R D
forward_state rightRD.lit := Fixed.optimized R D
theorem rightRD.lit_eq : Fixed.optimized R D=rightRD.lit := optimize_of_lit leftRD.lit_eq (by kernel_rfl)
materialize_value leftDR := Fixed.original D R
forward_state rightDR.lit := Fixed.optimized D R
theorem rightDR.lit_eq : Fixed.optimized D R=rightDR.lit := optimize_of_lit leftDR.lit_eq (by kernel_rfl)
materialize_value leftED := Fixed.original E D
forward_state rightED.lit := Fixed.optimized E D
theorem rightED.lit_eq : Fixed.optimized E D=rightED.lit := optimize_of_lit leftED.lit_eq (by kernel_rfl)

theorem rd_left : ∀ i∈Fixed.original R D,instrBound i≤992 := by
  rw [leftRD.lit_eq]; exact bound_of_listAllK (by decide +kernel)
private theorem rd_ok : listAllK (instrOkK 992 (RegSet.ofList (VG.Proof.Mont.AArch64.clob M.n)) [(0,992)])
    rightRD.lit=true := by decide +kernel
theorem rd_right : ∀ i∈Fixed.optimized R D,instrBound i≤992 := by
  rw [rightRD.lit_eq]; exact bound_of_instrOk rd_ok
theorem rd_clob : ∀ r∈(Fixed.optimized R D).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n := by
  rw [rightRD.lit_eq]; exact clob_of_instrOk rd_ok

theorem dr_left : ∀ i∈Fixed.original D R,instrBound i≤992 := by
  rw [leftDR.lit_eq]; exact bound_of_listAllK (by decide +kernel)
private theorem dr_ok : listAllK (instrOkK 992 (RegSet.ofList (VG.Proof.Mont.AArch64.clob M.n)) [(0,992)])
    rightDR.lit=true := by decide +kernel
theorem dr_right : ∀ i∈Fixed.optimized D R,instrBound i≤992 := by
  rw [rightDR.lit_eq]; exact bound_of_instrOk dr_ok
theorem dr_clob : ∀ r∈(Fixed.optimized D R).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n := by
  rw [rightDR.lit_eq]; exact clob_of_instrOk dr_ok

theorem ed_left : ∀ i∈Fixed.original E D,instrBound i≤992 := by
  rw [leftED.lit_eq]; exact bound_of_listAllK (by decide +kernel)
private theorem ed_ok : listAllK (instrOkK 992 (RegSet.ofList (VG.Proof.Mont.AArch64.clob M.n)) [(0,992)])
    rightED.lit=true := by decide +kernel
theorem ed_right : ∀ i∈Fixed.optimized E D,instrBound i≤992 := by
  rw [rightED.lit_eq]; exact bound_of_instrOk ed_ok
theorem ed_clob : ∀ r∈(Fixed.optimized E D).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n := by
  rw [rightED.lit_eq]; exact clob_of_instrOk ed_ok

end VG.Proof.Weierstrass.AArch64.Forward.P256Bounds
