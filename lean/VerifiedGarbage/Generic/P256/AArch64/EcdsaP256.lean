module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Data.BitVec
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
public import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.InvAllocated
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.Lit
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothLit
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Data.Finset.Card

/-!
# ECDSA over P-256 (FIPS 186-5) on AArch64

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.AArch64.EcdsaP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.P256.signApi.artifact AArch64.target {
    notes := ["The function saves `x19`–`x25` in its 8 KB \
      scratch buffer. Field elements and scalars are four 64-bit Montgomery words. `[k]G` \
      uses 37 width-7 Booth digits in `[-64,64]`, with no initial correction point. Each \
      affine entry is selected by scanning all 64 entries of its row in `VG_P256_COMB`; \
      sign correction uses a mask. From the lowest window upward, a Jacobian accumulator \
      uses mixed additions (8 products and 3 squares), specialized P-256 squaring, and \
      register forwarding between field operations. The Booth partial-sum and generator-order \
      proofs exclude equal nonzero inputs to the mixed formula. Infinity and zero-digit \
      cases use masks. The result is converted once to homogeneous coordinates `(XZ,Y,Z³)`. \
      Field and scalar inversions use 590 fixed divsteps in ten batches of 59. The signature \
      or zeros is selected by a validity mask. The loops, table accesses and arithmetic \
      have timing independent of the secret key, nonce and digest."]
    consts := Impl.Ecdsa.AArch64.p256.combConsts
    code := Impl.P256.Booth.sign
    verified := Proof.Ecdsa.AArch64.booth_sign_verified h.law h.inv (Proof.P256.combOk7 h.law) },
  Spec.Ecdsa.P256.verifyApi.artifact AArch64.target {
    notes := ["The function saves the callee-saved registers \
      `x19`–`x28` and `x30` in its 8 KB scratch buffer. Field elements and scalars are four \
      64-bit words in Montgomery form; field squares use the specialized P-256 Montgomery \
      square. The key is checked without branches, and multiplication uses the key's point \
      if valid, else `G`. The scalar inverse uses nine batches of 59 divsteps, with a tenth \
      batch when the public input requires it. `[u]G + [v]Q` uses one \
      joint Jacobian accumulator with width-7 and width-5 sparse signed digits, respectively. \
      Generator digits reuse the odd multiples in the first row of `VG_P256_COMB`. The eight \
      odd multiples of `Q` are built with co-Z arithmetic (ECDH's DBLU and ZADDU, adding `2Q` \
      at a shared `Z`), which also yields the `Z²` and `Z³` values they cache. The joint loop doubles \
      its accumulator in place with five squares and three products, each linear combination \
      (`12a − 9b`, `4a − b`, `3a − 8b`) reduced once (ECDH's doubling), specializes arithmetic to the sparse P-256 prime, and keeps \
      field values in scalar registers across operations with checked scheduling and allocation, \
      then converts once to homogeneous coordinates. Verification compares the projective \
      x-coordinate with `r` and, when in range, `r + n`, without a field inversion. Table \
      lookups, skipped zero digits and exceptional-point branches depend on the public key, \
      digest and signature already declared public by the contract. The result combines \
      the key and scalar checks, rejection of infinity, and `x ≡ r` modulo `n` into a mask."]
    consts := Impl.Ecdsa.AArch64.p256.combConsts
    code := Impl.Ecdsa.Verify.AArch64.P256Allocated.verify
    verified := Proof.Ecdsa.Verify.AArch64.allocatedVerify_verified h.law h.prime h.inv h.invToM (Proof.P256.combOk7 h.law) }]

end VG.Generic.P256.AArch64.EcdsaP256
