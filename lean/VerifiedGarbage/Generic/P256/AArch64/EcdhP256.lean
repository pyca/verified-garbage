import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P256.EcdhJac.Verified

/-!
# ECDH over P-256 (SP 800-56A) on AArch64

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/AArch64/Law.lean`.
-/

namespace VG.Generic.P256.AArch64.EcdhP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) : List Artifact := [
  { Spec.Ecdh.P256.exchangeApi with
    target := AArch64.target
    doc := Spec.Ecdh.P256.exchangeApi.doc (notes := ["The peer's encoding and coordinates are checked \
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
      the pointers; the public contract and 8192-byte scratch requirement are unchanged."])
    code := Impl.P256.EcdhJac.exchange
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi
    verified := Proof.P256.EcdhJac.verified h.law h.inv h.prime h.invToMP
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P256.AArch64.EcdhP256
