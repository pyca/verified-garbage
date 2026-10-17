module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA key generation (FIPS 186-5 A.1.3) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.Arm

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact Arm.target {
    notes := ["Baseline ARMv7, on the working space of the RSA key routines, in 32-bit limbs, and \
        their constant-time arithmetic: `p` and `q` swapped under the mask of `p < q`; \
        `lcm(p − 1, q − 1)` as `(p − 1)(q − 1)` divided by `gcd(p − 1, q − 1)`, its power of \
        two found by `8 p_len` halving steps under masks and its odd part by the binary \
        extended Euclidean algorithm; `d` by the inverse of `L mod e` modulo `e` for an odd \
        `e` (then `d = (L (e − x) + 1) / e`), or of `e` modulo `L` for an even one; `qInv`, \
        `dP` and `dQ` by the inverse and the long division; the checks as masks, the outputs \
        stored under the final one. The code branches only on `e` and on whether `d` is too \
        small (the status 2)."]
    code := Impl.RsaKeyGen.Arm.Key.code
    stack := 56
    verified := Proof.RsaKeyGen.Arm.Key.key_verified }]

end VG.Artifacts.RsaKeyGen.Arm
