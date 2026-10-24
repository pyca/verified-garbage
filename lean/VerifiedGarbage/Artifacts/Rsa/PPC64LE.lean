module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreVerified
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rsa.PPC64LE

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact PPC64LE.target {
    notes := ["n is checked a byte at a time, then read into the working space a byte at a time. \
        The model has no carry bit, so numbers are 32-bit digits: R² mod n by `128 w` modular \
        doublings of 1, each with the borrow of the subtraction of n in the sign bit and selected \
        with a mask. The nonvolatile registers it uses are saved in the working space's header."]
    code := Impl.Bignum.PPC64LE.Precompute.precompute
    verified := Proof.Bignum.PPC64LE.Pre.precompute_verified },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact PPC64LE.target {
    notes := ["The model has no carry bit, so numbers are 32-bit digits, in Montgomery form with \
        `R = 2^(64 w)`. `e` is read a byte at a time into a register saturated at `2^33`, and its 33 \
        bits are scanned from the top, each a square and a multiplication by the input with the \
        product selected by a mask of the bit, so the code is the same for every `e` of the same \
        length. `pre` is made safe before any arithmetic (`n` forced odd with its top word not zero, \
        `R² mod n` zeroed unless below `n`), which leaves the values of a valid modulus unchanged. \
        The nonvolatile registers it uses are saved in the working space's header."]
    code := Impl.Bignum.PPC64LE.PublicChecked.publicChecked
    verified := Proof.Bignum.PPC64LE.Pub.publicChecked_verified },
  Spec.Rsa.crtValuesApi.artifact PPC64LE.target {
    notes := ["`n` is checked as `vg_rsa_public_precompute` checks it; then the checks (`p q = n`, \
        as `n mod p = 0`, `n / p = q` and `p` odd, and `gcd(q, p | 1) = 1`) give a mask, the \
        arithmetic is the same whatever the key, and the results are stored masked. The model has \
        no carry bit, so numbers are 32-bit digits. The remainders and quotients are computed by \
        bit-serial division, `32 w` steps for `w`-digit numbers, and `qInv` by `64 w` steps of the \
        binary extended Euclidean algorithm modulo `p | 1`, each step's swaps and subtractions \
        under masks. The pointers and lengths stay in nonvolatile registers, saved with the \
        others it uses in the working space's header."]
    code := Impl.Rsa.PPC64LE.CrtValues.code
    verified := Proof.Rsa.PPC64LE.CrtValues.cv_verified },
  Spec.Rsa.checkKeyApi.artifact PPC64LE.target {
    notes := ["`e` is checked as `vg_rsa_public_precomputed_checked` checks it and `n` as \
        `vg_rsa_public_precompute` checks it, which are the only branches on the key. Then every \
        check of the private key is computed whatever its outcome and and'ed into a mask: `p q = n` \
        as `n / p = q`, `n mod p = 0` and `p` odd, by bit-serial division, `32 w` steps for \
        `w`-digit numbers; the comparisons by a subtraction's borrow; `e dP mod (p - 1)` and \
        `e dQ mod (q - 1)` by modular multiplication over the 33 bits of `e`, and `q qInv mod p` \
        over the `32 w` bits of `q`, each step's subtraction under a mask; and `d` by `d < n` and \
        `d mod (p - 1) = dP`, `d mod (q - 1) = dQ`. The model has no carry bit, so numbers are \
        32-bit digits. The pointers and lengths stay in nonvolatile registers, saved with the \
        others it uses in the working space's header."]
    code := Impl.Rsa.PPC64LE.CheckKey.code
    verified := Proof.Rsa.PPC64LE.KeyCheck.ck_verified },
  Spec.Rsa.checkCrtKeyApi.artifact PPC64LE.target {
    notes := ["`vg_rsa_check_key`'s code without the checks of `d`: `e` and `n` are checked first, \
        which are the only branches on the key; then every check of the private key is computed \
        whatever its outcome and and'ed into a mask."]
    code := Impl.Rsa.PPC64LE.CheckCrtKey.code
    verified := Proof.Rsa.PPC64LE.KeyCheck.cck_verified }]

end VG.Artifacts.Rsa.PPC64LE
