module

public import VerifiedGarbage.Proof.BrainpoolP256r1.Curve
public import Mathlib.Data.BitVec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
public import VerifiedGarbage.Proof.Weierstrass.InvArith
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.BrainpoolP256r1.Point
public import VerifiedGarbage.Proof.Divstep.Batch
public import VerifiedGarbage.Proof.Divstep.Tc
public import VerifiedGarbage.Proof.Divstep.Word
public import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
public import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
public import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
public import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
public import VerifiedGarbage.Proof.Weierstrass.Cubic
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.BrainpoolP256r1.Point
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Incl
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.BitByte
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.Weierstrass.Law3
import VerifiedGarbage.Proof.Weierstrass.Words

/-! # brainpoolP256r1's group law and inversions, on AArch64 -/

@[expose] public section

namespace VG.Variants.BrainpoolP256r1.AArch64.Law

open Proof.Weierstrass Proof.Weierstrass.AArch64

def variant : HasLawInv Spec.BrainpoolP256r1.curve :=
  ⟨Proof.BrainpoolP256r1.law, fun hp => invSound_of_toM hp (invToM_of_prime hp)⟩

end VG.Variants.BrainpoolP256r1.AArch64.Law
