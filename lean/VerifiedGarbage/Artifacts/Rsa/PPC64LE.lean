module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreVerified
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubVerified
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rsa.PPC64LE

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact PPC64LE.target {
    notes := ["n is checked a byte at a time, then read into the working space a byte at a time. \
        `R² mod n` starts from `2^(64 (w - 1))`, below a valid `n`: `64 + w` modular doublings, \
        each with the borrow of the subtraction of n in the sign bit and selected with a mask, give \
        `2^w R mod n`, and six Montgomery squares (radix `2^64`, with the carry bit) raise it to \
        `2^(64 w) R mod n = R² mod n`. The nonvolatile registers it uses are saved in the working \
        space's header."]
    code := Impl.Bignum.PPC64LE.Precompute.precompute
    verified := Proof.Bignum.PPC64LE.Pre.precompute_verified },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact PPC64LE.target {
    notes := ["Montgomery multiplication in radix `2^64` with the carry bit, `R = 2^(64 w)`. `e` is \
        read a byte at a time into a register saturated at `2^33`; the scan starts at its first set \
        bit with the input in Montgomery form, then each later bit is a Montgomery square and, if \
        set, a multiplication by the input in Montgomery form, but the last, whose multiplication is \
        by the ordinary input (or 1), which also converts out of Montgomery form: for 65537, sixteen \
        squares and one multiplication. The branches depend only on `e`, which is public. `pre` is \
        made safe before any arithmetic (`n` forced odd with its top word not zero, `R² mod n` zeroed \
        unless below `n`), which leaves the values of a valid modulus unchanged. The nonvolatile \
        registers it uses are saved in the working space's header."]
    code := Impl.Bignum.PPC64LE.PublicChecked.publicChecked
    verified := Proof.Bignum.PPC64LE.Pub.publicChecked_verified },
  Spec.Rsa.privateCrtApi.artifact PPC64LE.target {
    notes := ["Montgomery multiplication in radix `2^64` with the carry bit. The checks (`n` as \
        `vg_rsa_public_precompute` checks it, the input below `n`, `p q = n` by a Montgomery \
        product modulo `2^(64 w) - 1`, which is exact, `qInv < p`) give a mask; under a clear mask \
        the primes are replaced by 3 and `qInv` by 0, so that the arithmetic is the same whatever \
        the key, and the result is stored masked. Each prime has its own working space of 24 \
        numbers of `max(2, ⌈len/8⌉)` words for its public length: the input is reduced modulo it a \
        bit at a time, and the exponent is scanned in four-bit windows from the top, four \
        Montgomery squares and a multiplication by the table entry `x^d R` per window, the entry \
        selected by a masked scan of the whole 16-entry table on 64-bit words, so that no address \
        depends on the \
        exponent. `q h + m₂` is a Montgomery product modulo `2^(64 w) - 1` and an addition. The \
        nonvolatile registers it uses are saved in the working space's header."]
    code := Impl.Bignum.PPC64LE.Crt.crt
    verified := Proof.Bignum.PPC64LE.Crt.crt_verified },
  Spec.Rsa.privateCheckedApi.artifact PPC64LE.target {
    notes := ["This implementation computes the result `m` with `vg_rsa_private_crt` into its frame, \
        then `m^e mod n` with `vg_rsa_public_precompute` and `vg_rsa_public_precomputed_checked`, \
        which also checks `e`. It compares that with the input in constant time, and copies `m` to \
        `out` under a mask, which is clear unless the CRT and the public operation succeeded and the \
        two match. The result, 1, 2 or 0, is computed from the mask without a branch. Then it \
        overwrites the frame's copy of `m` with zeros. Its frame of 3328 bytes holds `m`, the \
        precomputed values of `n`, the statuses, the registers kept across the calls and the stack \
        arguments of the calls, whose callees use no stack."]
    code := Impl.Rsa.PPC64LE.Priv.code
    stack := Impl.Rsa.PPC64LE.Priv.frameBytes
    verified := Proof.Rsa.PPC64LE.Priv.priv_verified },
  Spec.Rsa.crtValuesApi.artifact PPC64LE.target {
    notes := ["`n` is checked as `vg_rsa_public_precompute` checks it; then the checks (`p q = n`, \
        as `n mod p = 0`, `n / p = q` and `p` odd, and `gcd(q, p | 1) = 1`) give a mask, the \
        arithmetic is the same whatever the key, and the results are stored masked. Numbers are \
        32-bit digits; for an even count of them the subtractions (the borrow in the carry bit), \
        selections, copies, comparisons and halvings, and the division's shifts, work on 64-bit \
        words, two digits at a time. The remainders and quotients are computed by \
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
        `d mod (p - 1) = dP`, `d mod (q - 1) = dQ`. Numbers are 32-bit digits; for an even count \
        of them the subtractions (the borrow in the carry bit), selections, copies, comparisons \
        and halvings, and the division's shifts, work on 64-bit words, two digits at a time. The \
        pointers and lengths stay in nonvolatile registers, saved with the \
        others it uses in the working space's header."]
    code := Impl.Rsa.PPC64LE.CheckKey.code
    verified := Proof.Rsa.PPC64LE.KeyCheck.ck_verified },
  Spec.Rsa.checkCrtKeyApi.artifact PPC64LE.target {
    notes := ["`vg_rsa_check_key`'s code without the checks of `d`: `e` and `n` are checked first, \
        which are the only branches on the key; then every check of the private key is computed \
        whatever its outcome and and'ed into a mask."]
    code := Impl.Rsa.PPC64LE.CheckCrtKey.code
    verified := Proof.Rsa.PPC64LE.KeyCheck.cck_verified },
  Spec.Rsa.recoverPrimesApi.artifact PPC64LE.target {
    notes := ["`n` is checked as `vg_rsa_public_precompute` checks it, the only branch on the key \
        but for the number of candidates tried, which is public. `m = d e - 1` is computed by \
        binary multiplication. Each candidate `g = 2, 3, …` makes one pass over the `⌈c / 32⌉` \
        32-bit digits of `m` (`c = 8 (e_len + d_len)`, leading zeros included), most significant \
        bit first, fusing the exponentiation with root detection: each bit is a Montgomery square \
        `x = y²` and `x g` (modular additions for the public candidates 2 and 3, a Montgomery \
        product for the others), the new `y` selected by a mask of the bit. A set bit starts root \
        detection again from the new `y` (`done := y = ±1`, `ok := 0`); a clear bit keeps the old \
        `y` as the root under a mask when `x = 1` and not done. Only the trailing zeros of `m` \
        can leave `ok` set, with the root of SP 800-56B Rev. 2 Appendix C.1's search. \
        `p = gcd(y - 1, n)` by `64 w` steps of the binary extended Euclidean algorithm, `q = n / p` \
        by bit-serial division, the order by a subtraction's borrow, and the factors stored masked \
        by `ok`. Montgomery products are on 64-bit words with the carry bit; the other arithmetic \
        is on 32-bit digits, two at a time as 64-bit words (the subtractions' borrow in the carry \
        bit) for an even count of them. The pointers and lengths stay in nonvolatile registers, saved with \
        the others it uses in the working space's arrays 44–45."]
    code := Impl.Rsa.PPC64LE.Recover.code
    verified := Proof.Rsa.PPC64LE.Recover.rv_verified }]

end VG.Artifacts.Rsa.PPC64LE
