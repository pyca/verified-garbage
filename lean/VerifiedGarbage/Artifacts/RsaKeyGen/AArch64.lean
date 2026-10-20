module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Verified
public import Aesop.BuiltinRules
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA key generation (FIPS 186-5 A.1.3) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.AArch64

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact AArch64.target {
    notes := ["Baseline AArch64, on the working space of the RSA key routines and their constant-time \
        arithmetic: `p` and `q` swapped under the mask of `p < q`; `lcm(p − 1, q − 1)` as \
        `(p − 1)(q − 1)` divided by `gcd(p − 1, q − 1)`, its power of two found by `64 W` halving \
        steps under masks and its odd part by the binary extended Euclidean algorithm; `d` by the \
        inverse of `L mod e` modulo `e` for an odd `e` (then `d = Q (e − x) + (1 + R (e − x)) / e`), \
        or of `e mod L` modulo `L` for an even one; `qInv`, `dP` and `dQ` by the inverse and the \
        division; the checks as masks, the outputs stored under the final one. The code branches \
        only on `e` and on whether `d` is too small (the status 2)."]
    code := Impl.RsaKeyGen.AArch64.Key.code
    verified := Proof.RsaKeyGen.AArch64.Key.key_verified }]

end VG.Artifacts.RsaKeyGen.AArch64
