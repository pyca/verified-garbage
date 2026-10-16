module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Verified
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA key generation (FIPS 186-5 A.1.3) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.X86_64

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact X86_64.target {
    notes := ["Baseline x86-64, on `vg_rsa_public`'s working space and the RSA key routines' \
        constant-time arithmetic: `p` and `q` swapped under the mask of `p < q`; \
        `lcm(p − 1, q − 1)` as `(p − 1)(q − 1)` divided by `gcd(p − 1, q − 1)`, its power of two \
        found by `64 W` halving steps under masks and its odd part by the binary extended \
        Euclidean algorithm; `d` by the inverse of `L mod e` modulo `e` for an odd `e` (then \
        `d = Q (e − x) + (1 + R (e − x)) / e`), or of `e mod L` modulo `L` for an even one; \
        `qInv`, `dP` and `dQ` by the inverse and the division; the checks as masks, the outputs \
        stored under the final one. The code branches only on `e` and on whether `d` is too \
        small (the status 2)."]
    code := Impl.RsaKeyGen.X86_64.Key.code
    verified := Proof.RsaKeyGen.X86_64.Key.key_verified }]

end VG.Artifacts.RsaKeyGen.X86_64
