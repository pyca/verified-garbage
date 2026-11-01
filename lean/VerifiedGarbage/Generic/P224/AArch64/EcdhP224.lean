module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Impl.Ecdh.P224.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.P224.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdh.AArch64.P224.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdh.P224
import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Ecdh.AArch64.P224.Verified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdh.Exchange
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
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
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
public import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! # ECDH over P-224 (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Generic.P224.AArch64.EcdhP224

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) : List Artifact := [
  Spec.Ecdh.P224.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.exchangeP224
    verified := Proof.Ecdh.AArch64.P224.ecdh_verified h.law h.inv }]

end VG.Generic.P224.AArch64.EcdhP224
