module

import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256RD
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.P256.VerifyRegisters
import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.Weierstrass.Mul

/-! The forwarded point doubling of P-256 verification (`VerifyDouble.double`) as a
literal, checked once for the joint and allocated verifications, which call it
from their table, cached additions and mixed additions (`Proof/Framework/Lit.lean`):
`Forward.P256RD`'s, by rewriting, rather than the kernel running the optimizer
again. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P256

noncomputable def double.lit : Prog isa := .block Proof.Weierstrass.AArch64.Forward.P256Bounds.rightRD.lit

theorem double.lit_eq :
    VerifyDouble.double P256Joint.cfg.K.M P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.D =
      double.lit := by
  change VerifyDouble.double VerifyDouble.M VerifyDouble.S VerifyDouble.R VerifyDouble.D = _
  rw [VerifyDouble.double, ite_eq_left (show VerifyDouble.selected VerifyDouble.M VerifyDouble.S
    VerifyDouble.R VerifyDouble.D from ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩)]
  exact congrArg Code.block Proof.Weierstrass.AArch64.Forward.P256RD.optimized_lit

/-- `double` as `P256Allocated.mixedAdd` writes it, with `P256Allocated.K`, which
is `P256Joint.cfg.K` by definition: `materialize_code` reads a literal where the
code has its left-hand side as written. -/
noncomputable abbrev doubleAllocated.lit := double.lit
theorem doubleAllocated.lit_eq :
    VerifyDouble.double P256Allocated.K.M P256Allocated.K.S P256Allocated.K.R P256Allocated.K.D =
      doubleAllocated.lit :=
  double.lit_eq

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
