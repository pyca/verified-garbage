module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Rsa.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubVerified

/-! # RSA (RFC 8017) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Rsa.X86_64

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact X86_64.target {
    notes := ["Baseline x86-64: for n whose top bit is set and whose number of words is a multiple \
        of 4, R² mod n from R - n by steps of long division, a word at a time (Knuth's Algorithm D, \
        each quotient digit by Möller and Granlund's division by a reciprocal of n's top word, with \
        its corrections by masks), then two squarings; for any other n, by constant-time doublings \
        and squarings. Montgomery multiplication by calls of `vg_rsa_mont_mul`."]
    code := Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.base.mm
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.precompute_verified },
  Spec.Rsa.publicPrecomputeApi.artifact X86_64.target {
    suffix := "_adx"
    notes := ["`vg_rsa_public_precompute`'s code, with Montgomery multiplication by calls of \
        `vg_rsa_mont_mul_adx`, and, for n whose top bit is set and whose number of words is a multiple of 4, \
        R² mod n from R - n by w steps of long division and no squarings: each quotient digit as there, \
        and the step `x 2^64 - q n` in one pass over the words with MULX and two carry chains (ADCX, ADOX), \
        n added back by a branch when the result is negative (n is public)."]
    code := Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Bignum.X86_64.R2Adx.choice Proof.Rsa.X86_64.CallMont.adx.mm)
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.precomputeAdx_verified
    features := ["bmi2", "adx"] },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact X86_64.target {
    notes := ["Baseline x86-64: `e` is checked first, its bytes read into a register saturated at \
        `2^34 - 1` once they reach `2^33`; then Montgomery multiplication on 64-bit words. The result \
        is the input raised to `e - 1` (`e` is odd): for `e = 65537` by sixteen squares, otherwise \
        with the exponent less one scanned left to right from its first set bit, which starts the \
        result as the input, a square per later bit and a multiplication per later set bit; then one \
        multiplication by the input itself adds the last bit and leaves Montgomery form at once. \
        `pre` is checked (`n` odd, its top word not zero, `R² mod n` below it) before any \
        arithmetic, so that values of no modulus are safe."]
    code := Impl.Rsa.X86_64.Folded.checked Proof.Bignum.X86_64.Mont.base.mm
    verified := Proof.Bignum.X86_64.FoldedPublic.base_verified },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact X86_64.target {
    suffix := "_adx"
    notes := ["The exponentiation of the baseline, with the last multiplication by the input itself. \
        Montgomery multiplication for a \
        number of words that is a multiple of 4 (from 4 to 2^30) adds `a_i b + u m` to the \
        accumulator in one pass per word of `a`, four words at a time, with BMI2's `mulx` and \
        ADX's `adcx` and `adox` (two carry chains at once), and is the baseline's otherwise."]
    code := Impl.Rsa.X86_64.Folded.checked Proof.Bignum.X86_64.Mont.adxSquare.mm
    verified := Proof.Bignum.X86_64.FoldedPublic.adx_verified
    features := ["bmi2", "adx"] },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact X86_64.target {
    suffix := "_ifma"
    notes := ["For `e = 65537` and a modulus of 32, 48 or 64 words: the input and `R² mod n` into numbers \
        of 52-bit limbs, then twenty Montgomery multiplications with AVX512_IFMA, as \
        `vg_rsa_private_crt_ifma`'s (one lane, the radix `R' = 2^(52 L)` for `4 L` limbs): \
        `R²` to `R'²` by a square and a product by `2^(208 L - 256 W)`, the input into Montgomery form, \
        sixteen squares and a last product by it; the result back to words and reduced once. Within \
        Intel's MXCSR prologue and epilogue. Otherwise `vg_rsa_public_precomputed_checked_adx`'s code."]
    code := Impl.Rsa.X86_64.PubIfma.checked Proof.Bignum.X86_64.Mont.adxSquare.mm
    verified := Proof.Bignum.X86_64.Ifma.Pub.ifma_verified
    features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"] },
  Spec.Rsa.privateCrtApi.artifact X86_64.target {
    notes := ["Baseline x86-64: the checks (`n` as `vg_rsa_public_precompute` checks it, the input \
        below `n`, `p q = n` by a product of the two, `qInv < p`) give a mask; the primes are \
        replaced by 3 under a clear mask, so that the arithmetic is the same whatever the key, and \
        the result is stored masked. Each prime has its own working space, with its own \
        Montgomery multiplication (by calls of `vg_rsa_mont_mul`); the input is reduced modulo it by \
        Montgomery reduction of chunks of its size, and the exponents are scanned left to right \
        over all their bits by a fixed window of 4 bits: four squares and a multiplication by the \
        window's power of the input, from a table of all 16 after the prime's working space, read \
        by a masked selection from every entry."]
    code := Impl.Rsa.X86_64.Crt.code Proof.Rsa.X86_64.CallMont.base.mm
      (Impl.Rsa.X86_64.Crt.expLoopS Proof.Rsa.X86_64.CallMont.lazyBase Proof.Rsa.X86_64.CallMont.base.mm
        Impl.Rsa.X86_64.Crt.tabSelect)
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.crt_verified },
  Spec.Rsa.privateCrtApi.artifact X86_64.target {
    suffix := "_adx"
    notes := ["`vg_rsa_private_crt`'s code, with Montgomery multiplication by calls of \
        `vg_rsa_mont_mul_adx`, and the exponents scanned by a fixed window of 5 bits: five squares and a \
        multiplication by the window's power, from a table of all 32, read by a masked selection four \
        words at a time in AVX2's 256-bit registers."]
    code := Impl.Rsa.X86_64.Crt.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Rsa.X86_64.Crt.expLoop5S Proof.Rsa.X86_64.CallMont.lazyAdx Proof.Rsa.X86_64.CallMont.adx.mm
        Impl.Rsa.X86_64.Crt.tabSelectV)
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.crtAdx_verified
    features := ["avx", "avx2", "bmi2", "adx"] },
  Spec.Rsa.privateCrtApi.artifact X86_64.target {
    suffix := "_ifma"
    notes := ["`vg_rsa_private_crt_adx`'s code, but for a modulus of 32, 48 or 64 words and primes of \
        half as many words each (2048-, 3072- and 4096-bit keys), whose exponentiations run at once in \
        radix 2^52 with AVX512_IFMA's `vpmadd52luq` and `vpmadd52huq` on 256-bit registers, `ymm0` to \
        `ymm31`: almost-Montgomery multiplications modulo both primes, a table of 16 powers of each \
        base, and a fixed window of 4 bits over the exponents padded with zeros to the primes' size, \
        the table read by a masked selection from every entry. MXCSR is set to `0x1FBF` around the \
        vector code, as Intel's guidance for data-operand-independent timing asks, and restored after \
        it."]
    code := Impl.Rsa.X86_64.CrtIfma.code Proof.Rsa.X86_64.CallMont.adx.mm
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.crtIfma_verified
    features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"] },
  Spec.Rsa.privateCrtPrecomputedApi.artifact X86_64.target {
    notes := ["`vg_rsa_private_crt`'s code, with `R² mod n` and each prime's `R_X mod X` copied from \
        `pre` (its words at `n_len`'s words, then at twice them, then past `p`'s) instead of computed. \
        Each value copied is masked by the borrow of its comparison with its modulus: it is zero unless it \
        is below the modulus, so that a wrong `pre` never puts a number past the modulus in the arithmetic."]
    code := Impl.Rsa.X86_64.Crt.code Proof.Rsa.X86_64.CallMont.base.mm
      (Impl.Rsa.X86_64.Crt.expLoopS Proof.Rsa.X86_64.CallMont.lazyBase Proof.Rsa.X86_64.CallMont.base.mm
        Impl.Rsa.X86_64.Crt.tabSelect) true
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.crtPre_verified },
  Spec.Rsa.privateCrtPrecomputedApi.artifact X86_64.target {
    suffix := "_adx"
    notes := ["`vg_rsa_private_crt_adx`'s code, with the values from `pre` as \
        `vg_rsa_private_crt_precomputed` takes them."]
    code := Impl.Rsa.X86_64.Crt.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Rsa.X86_64.Crt.expLoop5S Proof.Rsa.X86_64.CallMont.lazyAdx Proof.Rsa.X86_64.CallMont.adx.mm
        Impl.Rsa.X86_64.Crt.tabSelectV) true
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.crtPreAdx_verified
    features := ["avx", "avx2", "bmi2", "adx"] },
  Spec.Rsa.privateCrtPrecomputedApi.artifact X86_64.target {
    suffix := "_ifma"
    notes := ["`vg_rsa_private_crt_ifma`'s code, with the values from `pre` as \
        `vg_rsa_private_crt_precomputed` takes them."]
    code := Impl.Rsa.X86_64.CrtIfma.code Proof.Rsa.X86_64.CallMont.adx.mm true
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.crtPreIfma_verified
    features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"] },
  Spec.Rsa.crtValuesApi.artifact X86_64.target {
    notes := ["Baseline x86-64: `n` is checked as `vg_rsa_public_precompute` checks it; then the \
        checks (`p q = n`, as `n mod p = 0`, `n / p = q` and `p` odd, and `gcd(q, p) = 1`) give a \
        mask, the arithmetic is the same whatever the key, and the results are stored masked. The \
        remainders and quotients are computed by bit-serial division, `64 w` steps for `w`-word \
        numbers, and `qInv` by `128 w` steps of the binary extended Euclidean algorithm modulo `p`, \
        each step's swaps and subtractions under masks."]
    code := Impl.Rsa.X86_64.Keys.CrtValues.code
    verified := Proof.Rsa.X86_64.Instances.crtValues_verified },
  Spec.Rsa.recoverPrimesApi.artifact X86_64.target {
    notes := ["Baseline x86-64: `n` is checked as `vg_rsa_public_precompute` checks it; `d e` and \
        the halvings of `d e - 1` (`r` odd and `t` its twos) run over `64 Bw` steps for `Bw` words \
        of `d e`, whatever their values. Each candidate `g` computes `g^r mod n` by \
        Montgomery multiplication (by calls of `vg_rsa_mont_mul`) over all the bits of `r`, a square and a multiplication by `g` or \
        1 (a masked selection) per bit, then `64 Bw` squarings, each kept or not under masks; the \
        candidates stop at the first that finds the factors, which is the only branch on the key. \
        `gcd(y - 1, n)` is `128 w` steps of the binary extended Euclidean algorithm, and `n / p` \
        `64 w` steps of bit-serial division."]
    code := Impl.Rsa.X86_64.Keys.Recover.code Proof.Rsa.X86_64.CallMont.base.mm
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.recover_verified },
  Spec.Rsa.recoverPrimesApi.artifact X86_64.target {
    suffix := "_adx"
    notes := ["`vg_rsa_recover_primes`'s code, with Montgomery multiplication by calls of \
        `vg_rsa_mont_mul_adx`."]
    code := Impl.Rsa.X86_64.Keys.Recover.code Proof.Rsa.X86_64.CallMont.adx.mm
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.recoverAdx_verified
    features := ["bmi2", "adx"] },
  Spec.Rsa.checkKeyApi.artifact X86_64.target {
    notes := ["Baseline x86-64: `e` is checked as `vg_rsa_public_precomputed_checked` checks it and \
        `n` as `vg_rsa_public_precompute` checks it, which are the only branches on the key. Then every check \
        of the private key is computed whatever its outcome and and'ed into a mask: the comparisons by \
        a subtraction's borrow over `w` words, `p q = n` by a product of the two, and each remainder \
        (`d e mod (p - 1)` and the others, `q qInv mod p`) by restoring division, a doubling modulo \
        the divisor per bit of the product, `64 (w + 2)` or `64 (2 w + 2)` bits for `w`-word \
        numbers, its subtraction selected under a mask."]
    code := Impl.Rsa.X86_64.CheckKey.code
    verified := Proof.Rsa.X86_64.Instances.checkKey_verified },
  Spec.Rsa.checkCrtKeyApi.artifact X86_64.target {
    notes := ["Baseline x86-64: `vg_rsa_check_key`'s code without the checks of `d`. `e` and `n` \
        are checked first, which are the only branches on the key; then every check of the private key is \
        computed whatever its outcome and and'ed into a mask. Each remainder (`e dP mod (p - 1)`, \
        `e dQ mod (q - 1)`, `q qInv mod p`) is computed by restoring division over numbers as long as the \
        divisor, starting from the product's words above its low `c` (`c = 1`, or `⌈q_len / 8⌉` for \
        `q qInv`), which are below the divisor when the comparison before it holds: `64 c` doublings \
        modulo the divisor rather than one per bit of the product."]
    code := Impl.Rsa.X86_64.CheckCrtKey.code
    verified := Proof.Rsa.X86_64.Instances.checkCrtKey_verified }]

end VG.Artifacts.Rsa.X86_64
