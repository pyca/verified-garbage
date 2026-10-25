module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA key generation (FIPS 186-5 A.1.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact PPC64LE.target {
    notes := ["On the working space of the RSA key routines, in 32-bit digits (its subtractions, \
        with the borrow in the carry bit, selections, copies, comparisons and halvings, and the \
        division's shifts, on 64-bit words for an even count of digits), with no branch but the \
        loops', whose counts depend only on the lengths: \
        `p` and `q` swapped under the mask of `p < q`; `lcm(p − 1, q − 1)` as \
        `(p − 1)(q − 1)` (bit-serial multiplication) divided by `gcd(p − 1, q − 1)`, its power \
        of two found by `8 p_len` halving steps under masks and its odd part by the binary \
        extended Euclidean algorithm; `d` for every case of `e`, selected by masks: for an odd \
        `e`, `L = e Q + R` and the inverse `x` of `R` modulo `e`, then \
        `d = Q (e − x) + (R (e − x) + 1) / e`; for an even one, the inverse of `e` modulo `L`; \
        `qInv`, `dP` and `dQ` by the inverse and the long division; the checks as masks, the \
        outputs stored under the final one. The pointers and lengths stay in nonvolatile \
        registers, saved with the others it uses in the working space's header."]
    code := Impl.RsaKeyGen.PPC64LE.Key.code
    verified := Proof.RsaKeyGen.PPC64LE.Key.key_verified }]

end VG.Artifacts.RsaKeyGen.PPC64LE
