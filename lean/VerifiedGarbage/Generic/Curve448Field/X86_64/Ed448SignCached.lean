module

public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Verified
import VerifiedGarbage.Proof.Ed448.X86_64.VariantVerified
import VerifiedGarbage.Proof.Ed448.Facts
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Ed448.X86_64.SignCached
public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLit
public import VerifiedGarbage.Proof.Sha3.X86_64.Round

/-!
# Ed448 signing with a cached public key on x86-64

The signature and documentation come from the reviewed Ed448 API. The proof
of `vg_ed448_scalar_base` is passed to the caller's here, so that only this
file imports it, with the reference ladder's agreement with the specification
(`Proof/Ed448/Facts.lean`).
-/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Ed448SignCached

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.Ed448.signCachedApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    notes := ["Uses the selected field backend and baseline integer instructions elsewhere. \
      Hashes the private key, `dom4(0, C) || prefix || M` and `dom4(0, C) || R || A || M` with \
      `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` (SHAKE256, with the Keccak \
      state and the sponge functions' working space in `scratch`) into a stack frame; prunes \
      the scalar `s` there; reduces the nonce `r` and the challenge `k` with \
      `vg_ed448_scalar_reduce`; writes `R = [r]B` with `vg_ed448_scalar_base` and \
      `S = (r + k s) mod L` with `vg_ed448_scalar_mul_add` into `out`; and clears `s` and `r` \
      from the frame. The hashes, and the scalar operations' working values, are left in \
      `scratch`."]
    code := Impl.Ed448.X86_64.SignCached.signCachedFor v
    stack := 464
    verified := Proof.Ed448.X86_64.SignCached.signCached_verified
      (Proof.Ed448.X86_64.scalarBaseFor_ok v Proof.Ed448.baseLadder_ok)
      (Proof.Ed448.X86_64.scalarBaseFor_ct v) }]

end VG.Generic.Curve448Field.X86_64.Ed448SignCached
