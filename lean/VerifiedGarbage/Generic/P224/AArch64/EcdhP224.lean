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
public import VerifiedGarbage.Spec.Weierstrass.Mul
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
import VerifiedGarbage.Spec.Weierstrass.Mul

/-!
# ECDH over P-224 (SP 800-56A) on AArch64

A generic file (see `TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.AArch64.EcdhP224

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) : List Artifact := [
  Spec.Ecdh.P224.exchangeApi.artifact AArch64.target {
    notes := ["The function is `vg_ecdsa_p224_sign`'s \
      setup, field arithmetic and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers `x19`–`x25` in `scratch`; field elements are four 64-bit words in \
      Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, with `mul` \
      and `umulh` and the multiplicand's words in registers; each reduction step multiplies the \
      accumulator's low word by `-p⁻¹ mod 2⁶⁴` and adds that multiple of `p`) with a final \
      conditional subtraction. The peer's key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and the scalar multiplication runs on \
      the peer's point if it is valid, else `G`, so always on a point of the curve. `[d]P` is by \
      signed 4-bit windows: `d + 8 Σ_{j<65} 16^j` gives 65 digits in `[-8, 7]`, a table of `[1 … \
      8]P` is built in `scratch`, and each digit takes four doublings (in Jacobian coordinates, \
      dbl-2001-b, with `Y = 1` where the result is the point at infinity) and the addition of \
      its entry, every entry loaded and masked and `y` negated by a mask of the digit's sign, by \
      the complete formula of Renes, Costello and Batina for `a = -3` (Algorithm 4); `Z⁻¹` is a \
      call of `vg_p224_inv_mod_p`, by divsteps (Bernstein and Yang's safegcd, half-delta form): 10 batches of 59 divsteps on the \
      low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each giving a matrix of 64-bit \
      entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` (divided by \
      2⁶⁴ modulo `p`, as in Montgomery reduction), 590 divsteps in all, enough for 256-bit \
      moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is \
      `a` times a constant or its negation by `f`'s sign. The number of steps is fixed, so the \
      time does not depend on `Z`. The result (or zeros) is selected by a mask of the checks, \
      `d` in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.Ecdh.AArch64.exchangeP224
    verified := Proof.Ecdh.AArch64.P224.ecdh_verified h.law h.inv }]

end VG.Generic.P224.AArch64.EcdhP224
