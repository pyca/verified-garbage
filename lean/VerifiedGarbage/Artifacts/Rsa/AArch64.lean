import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Rsa.AArch64.PubChecked
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.CrtVerified
import VerifiedGarbage.Proof.Rsa.AArch64.CvVerified
import VerifiedGarbage.Proof.Rsa.AArch64.CkVerified
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyVerified
import VerifiedGarbage.Proof.Rsa.AArch64.RpVerified

/-! # RSA (RFC 8017) on AArch64 -/

namespace VG.Artifacts.Rsa.AArch64

def artifacts : List Artifact := [
  { Spec.Rsa.publicCheckedApi with
    target := AArch64.target
    doc := Spec.Rsa.publicCheckedApi.doc
      (notes := ["Baseline AArch64: `e` is checked first, its bytes read into a register saturated at \
        `2^34 - 1` once they reach `2^33`; then Montgomery multiplication on 64-bit words (coarsely \
        integrated operand scanning with `mul` and `umulh`, the final subtraction selected with \
        `csel`), with R² mod n by constant-time doublings and squarings, and the exponent scanned \
        left to right from its first set bit, which starts the result as the input; a square per \
        later bit and a multiplication per later set bit."])
    code := Impl.Rsa.AArch64.Checked.publicChecked
    contract := Spec.Rsa.publicCheckedContract AArch64.abi
    verified := Proof.Rsa.AArch64.publicChecked_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rsa.publicPrecomputeApi with
    target := AArch64.target
    doc := Spec.Rsa.publicPrecomputeApi.doc
      (notes := ["Baseline AArch64: R² mod n as `vg_rsa_public_checked` computes it."])
    code := Impl.Rsa.AArch64.Precompute.code Proof.Bignum.AArch64.Mont.base.mm
    contract := Spec.Rsa.publicPrecomputeContract AArch64.abi
    verified := Proof.Bignum.AArch64.precompute_verified _
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rsa.publicPrecomputedCheckedApi with
    target := AArch64.target
    doc := Spec.Rsa.publicPrecomputedCheckedApi.doc
      (notes := ["Baseline AArch64: `e` is checked as `vg_rsa_public_checked` checks it; then Montgomery \
        multiplication and the exponentiation as `vg_rsa_public_checked`'s. `pre` is checked (`n` odd, \
        its top word not zero, `R² mod n` below it) before any arithmetic, so that values of no modulus \
        are safe."])
    code := Impl.Rsa.AArch64.Checked.precomputedChecked Proof.Bignum.AArch64.Mont.base.mm
    contract := Spec.Rsa.publicPrecomputedCheckedContract AArch64.abi
    verified := Proof.Rsa.AArch64.precomputedChecked_verified _
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rsa.privateCrtApi with
    target := AArch64.target
    doc := Spec.Rsa.privateCrtApi.doc
      (notes := ["Baseline AArch64: the checks (`n` as `vg_rsa_public_precompute` checks it, the input \
        below `n`, `p q = n` by a product of the two, `qInv < p`) give a mask; the primes are \
        replaced by 3 under a clear mask, so that the arithmetic is the same whatever the key, and \
        the result is stored masked. Each prime has its own working space, with its own \
        Montgomery multiplication (`vg_rsa_public_checked`'s); the input is reduced modulo it by \
        Montgomery reduction of chunks of its size, and the exponents are scanned left to right \
        over all their bits by a fixed window of 4 bits: four squares and a multiplication by the \
        window's power of the input, from a table of all 16 after the prime's working space, read \
        by a masked selection from every entry."])
    code := Impl.Rsa.AArch64.Crt.code Proof.Bignum.AArch64.Mont.base.mm
    contract := Spec.Rsa.privateCrtContract AArch64.abi
    verified := Proof.Bignum.AArch64.crt_verified _
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rsa.crtValuesApi with
    target := AArch64.target
    doc := Spec.Rsa.crtValuesApi.doc
      (notes := ["Baseline AArch64: `n` is checked as `vg_rsa_public_precompute` checks it; then the \
        checks (`p q = n`, as `n mod p = 0`, `n / p = q` and `p` odd, and `gcd(q, p) = 1`) give a \
        mask, the arithmetic is the same whatever the key, and the results are stored masked. The \
        remainders and quotients are computed by bit-serial division, `64 w` steps for `w`-word \
        numbers, and `qInv` by `128 w` steps of the binary extended Euclidean algorithm modulo `p`, \
        each step's swaps and subtractions under masks."])
    code := Impl.Rsa.AArch64.Keys.CrtValues.code
    contract := Spec.Rsa.crtValuesContract AArch64.abi
    verified := Proof.Rsa.AArch64.cv_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rsa.recoverPrimesApi with
    target := AArch64.target
    doc := Spec.Rsa.recoverPrimesApi.doc
      (notes := ["Baseline AArch64: `n` is checked as `vg_rsa_public_precompute` checks it; `d e` and \
        the halvings of `d e - 1` (`r` odd and `t` its twos) run over `64 Bw` steps for `Bw` words \
        of `d e`, whatever their values. Each candidate `g` computes `g^r mod n` by `vg_rsa_public_checked`'s \
        Montgomery multiplication over all the bits of `r`, a square and a multiplication by `g` or \
        1 (a masked selection) per bit, then `64 Bw` squarings, each kept or not under masks; the \
        candidates stop at the first that finds the factors, which is the only branch on the key. \
        `gcd(y - 1, n)` is `128 w` steps of the binary extended Euclidean algorithm, and `n / p` \
        `64 w` steps of bit-serial division."])
    code := Impl.Rsa.AArch64.Recover.code Proof.Bignum.AArch64.Mont.base.mm
    contract := Spec.Rsa.recoverPrimesContract AArch64.abi
    verified := Proof.Rsa.AArch64.rp_verified _
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rsa.checkKeyApi with
    target := AArch64.target
    doc := Spec.Rsa.checkKeyApi.doc
      (notes := ["Baseline AArch64: `e` is checked as `vg_rsa_public_checked` checks it and `n` as \
        `vg_rsa_public_precompute` checks it, which are the only branches on the key. Then every check \
        of the private key is computed whatever its outcome and and'ed into a mask, in a working space \
        of `W = 2 w + 2` words for `w`-word numbers: the comparisons by a subtraction's borrow, \
        `p q = n` by a product of the two, and each remainder (`d e mod (p - 1)` and the others, \
        `q qInv mod p`) by bit-serial division of the product, `64 W` steps, each subtraction selected \
        under a mask."])
    code := Impl.Rsa.AArch64.CheckKey.code
    contract := Spec.Rsa.checkKeyContract AArch64.abi
    verified := Proof.Rsa.AArch64.ck_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rsa.checkCrtKeyApi with
    target := AArch64.target
    doc := Spec.Rsa.checkCrtKeyApi.doc
      (notes := ["Baseline AArch64: `vg_rsa_check_key`'s code without the checks of `d`. `e` and `n` \
        are checked first, which are the only branches on the key; then every check of the private key is \
        computed whatever its outcome and and'ed into a mask. Each remainder (`e dP mod (p - 1)`, \
        `e dQ mod (q - 1)`, `q qInv mod p`) is computed by bit-serial division in the layout's \
        `W = 2 w + 2` words, starting from the product's words above its low `c` (`c = 1`, or \
        `⌈q_len / 8⌉` for `q qInv`), which are below the divisor when the comparison before it holds: \
        `64 c` steps rather than `64 W`."])
    code := Impl.Rsa.AArch64.CheckCrtKey.code
    contract := Spec.Rsa.checkCrtKeyContract AArch64.abi
    verified := Proof.Rsa.AArch64.ckc_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Rsa.AArch64
