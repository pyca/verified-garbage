module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P521.Comb7
public import VerifiedGarbage.Impl.EcKey.P521.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.P521.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.P521.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.Proof.EcKey.AArch64.P521.Verified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.P521.AArch64
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.P521.Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Spec.Weierstrass.Mul
import VerifiedGarbage.Impl.Ecdh.P521.AArch64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Spec.Weierstrass.Mul

/-!
# P-521 public keys (FIPS 186-5 §A.2) on AArch64

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.AArch64.EcP521

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P521.curve) : List Artifact := [
  Spec.EcKey.P521.publicKeyApi.artifact AArch64.target {
    notes := ["The function is `vg_ecdsa_p521_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it saves \
      the callee-saved registers `x19`–`x25` in `scratch`; field elements are nine \
      64-bit words in Montgomery form, multiplied by calls of `vg_p521_mul_mod_p` (word-by-word \
      Montgomery multiplication with all of `[b]` in registers, whose reductions are shifts, \
      P-521's `p` being friendly, and a final conditional subtraction); \
      `[d]G` is `vg_ecdsa_p521_sign`'s fixed-base comb of 7-bit signed digits from the 83 tables \
      of `[m 2^(7j)]G` (`m = 1 … 64`) in the static `VG_P521_COMB`, each entry selected in \
      constant time by loading the whole table, with no doublings; and \
      `Z⁻¹` is by divsteps (Bernstein and Yang's safegcd, half-delta form): 23 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 1357 divsteps in all, enough for \
      576-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z`. The result (or zeros) is selected by a \
      mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    consts := Impl.Ecdsa.AArch64.p521.combConsts
    code := Impl.EcKey.AArch64.publicKeyP521
    verified := Proof.EcKey.AArch64.P521.pk_verified h.law h.inv (Proof.P521.combOk7 h.law) }]

end VG.Generic.P521.AArch64.EcP521
