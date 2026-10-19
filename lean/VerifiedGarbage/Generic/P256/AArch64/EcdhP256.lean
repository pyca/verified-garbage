module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P256.EcdhJac.Verified
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Data.BitVec
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ecdh.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.P256.EcdhInverse.Update
public import VerifiedGarbage.Proof.P256.EcdhJac.DbluCertificate
public import VerifiedGarbage.Proof.P256.EcdhJac.Lit
public import VerifiedGarbage.Proof.P256.EcdhJac.OutCertificate
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
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdh.P256
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.ClearExcept
import Mathlib.Data.Finset.Card

/-!
# ECDH over P-256 (SP 800-56A) on AArch64

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.AArch64.EcdhP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) : List Artifact := [
  Spec.Ecdh.P256.exchangeApi.artifact AArch64.target {
    notes := ["The peer's encoding and coordinates are checked \
      without branches. Scalar multiplication uses the peer's point when it is valid and the \
      generator otherwise. Field elements are four 64-bit Montgomery words. Signed 5-bit \
      windows recode the scalar as `d + 16 Σ_{j<52} 32^j`; a 16-entry Jacobian table is built \
      with co-Z doubling and additions and stores each point's `Z²` and `Z³`. The first digit \
      initializes the accumulator, followed by 51 iterations of five Jacobian doublings and \
      one cached Jacobian addition. Each selection scans all 16 entries with NEON masks, and \
      digit signs, zero digits and infinity accumulators are handled without secret branches \
      or secret addresses. Prime-order bounds establish the nonexceptional additions for \
      valid private scalars; invalid scalars still execute safely and are rejected by the \
      existing final range check. Register-allocated point arithmetic uses explicit scratch \
      spills and restores the additional ABI registers and live output pointer. Inversion \
      retains the fixed 590-divstep schedule. The result or zeros is selected by the input \
      checks, `d` in `[1, n-1]`, and a nonzero projective denominator. Time depends only on \
      the pointers; the public contract and 8192-byte scratch requirement are unchanged."]
    code := Impl.P256.EcdhJac.exchange
    verified := Proof.P256.EcdhJac.verified h.law h.inv h.prime h.invToMP }]

end VG.Generic.P256.AArch64.EcdhP256
