import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Bignum.X86_64.PdVerified
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaVerified
import VerifiedGarbage.Proof.Rsa.X86_64.CvVerified
import VerifiedGarbage.Proof.Rsa.X86_64.RpVerified

/-! # RSA (RFC 8017) on x86-64 -/

namespace VG.Artifacts.Rsa.X86_64

def artifacts : List Artifact := [
  { Spec.Rsa.publicApi with
    target := X86_64.target
    doc := Spec.Rsa.publicApi.doc
      (notes := ["Baseline x86-64: Montgomery multiplication on 64-bit words, with R² mod n by \
        constant-time doublings and squarings, and the exponent scanned left to right, a square \
        per bit and a multiplication per set bit."])
    code := Impl.Bignum.X86_64.Public.code
    contract := Spec.Rsa.publicContract X86_64.abi
    verified := Proof.Bignum.X86_64.public_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.publicPrecomputeApi with
    target := X86_64.target
    doc := Spec.Rsa.publicPrecomputeApi.doc
      (notes := ["Baseline x86-64: R² mod n as `vg_rsa_public` computes it."])
    code := Impl.Rsa.X86_64.Precompute.code Proof.Bignum.X86_64.Mont.base.mm
    contract := Spec.Rsa.publicPrecomputeContract X86_64.abi
    verified := Proof.Bignum.X86_64.precompute_verified _ (by decide +kernel)
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.publicPrecomputeApi with
    target := X86_64.target
    name := Spec.Rsa.publicPrecomputeApi.name ++ "_adx"
    doc := Spec.Rsa.publicPrecomputeApi.doc
      (notes := ["`vg_rsa_public_precompute`'s code, with `vg_rsa_public_precomputed_adx`'s \
        Montgomery multiplication."])
    code := Impl.Rsa.X86_64.Precompute.code Proof.Bignum.X86_64.Mont.adx.mm
    contract := Spec.Rsa.publicPrecomputeContract X86_64.abi
    verified := Proof.Bignum.X86_64.precompute_verified _ (by decide +kernel)
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.publicPrecomputedApi with
    target := X86_64.target
    doc := Spec.Rsa.publicPrecomputedApi.doc
      (notes := ["Baseline x86-64: `vg_rsa_public`'s Montgomery multiplication, with the exponent \
        scanned left to right from its first set bit, which starts the result as the input; a \
        square per later bit and a multiplication per later set bit. `pre` is checked (`n` odd, \
        its top word not zero, `R² mod n` below it) before any arithmetic, so that values of no \
        modulus are safe."])
    code := Impl.Rsa.X86_64.Precomputed.code Proof.Bignum.X86_64.Mont.base.mm
    contract := Spec.Rsa.publicPrecomputedContract X86_64.abi
    verified := Proof.Bignum.X86_64.precomputed_verified _ (by decide +kernel)
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.publicPrecomputedApi with
    target := X86_64.target
    name := Spec.Rsa.publicPrecomputedApi.name ++ "_adx"
    doc := Spec.Rsa.publicPrecomputedApi.doc
      (notes := ["`vg_rsa_public_precomputed`'s code but for Montgomery multiplication, which for a \
        number of words that is a multiple of 4 (from 4 to 2^30) adds `a_i b + u m` to the \
        accumulator in one pass per word of `a`, four words at a time, with BMI2's `mulx` and \
        ADX's `adcx` and `adox` (two carry chains at once), and is the baseline's otherwise."])
    code := Impl.Rsa.X86_64.Precomputed.code Proof.Bignum.X86_64.Mont.adx.mm
    contract := Spec.Rsa.publicPrecomputedContract X86_64.abi
    verified := Proof.Bignum.X86_64.precomputed_verified _ (by decide +kernel)
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.privateCrtApi with
    target := X86_64.target
    doc := Spec.Rsa.privateCrtApi.doc
      (notes := ["Baseline x86-64: the checks (`n` as `vg_rsa_public_precompute` checks it, the input \
        below `n`, `p q = n` by a product of the two, `qInv < p`) give a mask; the primes are \
        replaced by 3 under a clear mask, so that the arithmetic is the same whatever the key, and \
        the result is stored masked. Each prime has its own working space, with its own \
        Montgomery multiplication (`vg_rsa_public`'s); the input is reduced modulo it by \
        Montgomery reduction of chunks of its size, and the exponents are scanned left to right \
        over all their bits by a fixed window of 4 bits: four squares and a multiplication by the \
        window's power of the input, from a table of all 16 after the prime's working space, read \
        by a masked selection from every entry."])
    code := Impl.Rsa.X86_64.Crt.code Proof.Bignum.X86_64.Mont.base.mm
    contract := Spec.Rsa.privateCrtContract X86_64.abi
    verified := Proof.Bignum.X86_64.crt_verified _ (by decide +kernel)
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.privateCrtApi with
    target := X86_64.target
    name := Spec.Rsa.privateCrtApi.name ++ "_adx"
    doc := Spec.Rsa.privateCrtApi.doc
      (notes := ["`vg_rsa_private_crt`'s code, with `vg_rsa_public_precomputed_adx`'s Montgomery \
        multiplication."])
    code := Impl.Rsa.X86_64.Crt.code Proof.Bignum.X86_64.Mont.adx.mm
    contract := Spec.Rsa.privateCrtContract X86_64.abi
    verified := Proof.Bignum.X86_64.crt_verified _ (by decide +kernel)
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.privateCrtApi with
    target := X86_64.target
    name := Spec.Rsa.privateCrtApi.name ++ "_ifma"
    doc := Spec.Rsa.privateCrtApi.doc
      (notes := ["`vg_rsa_private_crt_adx`'s code, but for a modulus of 32 words and primes of 16 words \
        each, whose exponentiations run at once in radix 2^52 with AVX512_IFMA's `vpmadd52luq` and \
        `vpmadd52huq` on 256-bit registers: almost-Montgomery multiplications modulo both primes, a \
        table of 16 powers of each base, and a fixed window of 4 bits over the exponents padded with \
        zeros to 128 bytes, the table read by a masked selection from every entry. MXCSR is set to \
        `0x1FBF` around the vector code, as Intel's guidance for data-operand-independent timing asks, \
        and restored after it."])
    code := Impl.Rsa.X86_64.CrtIfma.code Proof.Bignum.X86_64.Mont.adx.mm
    contract := Spec.Rsa.privateCrtContract X86_64.abi
    verified := Proof.Bignum.X86_64.ifma_verified _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
    features := ["avx", "avx2", "avx512ifma", "avx512vl", "bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.crtValuesApi with
    target := X86_64.target
    doc := Spec.Rsa.crtValuesApi.doc
      (notes := ["Baseline x86-64: `n` is checked as `vg_rsa_public_precompute` checks it; then the \
        checks (`p q = n`, as `n mod p = 0`, `n / p = q` and `p` odd, and `gcd(q, p) = 1`) give a \
        mask, the arithmetic is the same whatever the key, and the results are stored masked. The \
        remainders and quotients are computed by bit-serial division, `64 w` steps for `w`-word \
        numbers, and `qInv` by `128 w` steps of the binary extended Euclidean algorithm modulo `p`, \
        each step's swaps and subtractions under masks."])
    code := Impl.Rsa.X86_64.Keys.CrtValues.code
    contract := Spec.Rsa.crtValuesContract X86_64.abi
    verified := Proof.Rsa.X86_64.cv_verified (by decide +kernel)
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.recoverPrimesApi with
    target := X86_64.target
    doc := Spec.Rsa.recoverPrimesApi.doc
      (notes := ["Baseline x86-64: `n` is checked as `vg_rsa_public_precompute` checks it; `d e` and \
        the halvings of `d e - 1` (`r` odd and `t` its twos) run over `64 Bw` steps for `Bw` words \
        of `d e`, whatever their values. Each candidate `g` computes `g^r mod n` by `vg_rsa_public`'s \
        Montgomery multiplication over all the bits of `r`, a square and a multiplication by `g` or \
        1 (a masked selection) per bit, then `64 Bw` squarings, each kept or not under masks; the \
        candidates stop at the first that finds the factors, which is the only branch on the key. \
        `gcd(y - 1, n)` is `128 w` steps of the binary extended Euclidean algorithm, and `n / p` \
        `64 w` steps of bit-serial division."])
    code := Impl.Rsa.X86_64.Keys.Recover.code Proof.Bignum.X86_64.Mont.base.mm
    contract := Spec.Rsa.recoverPrimesContract X86_64.abi
    verified := Proof.Rsa.X86_64.rp_verified _ (by decide +kernel)
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.recoverPrimesApi with
    target := X86_64.target
    name := Spec.Rsa.recoverPrimesApi.name ++ "_adx"
    doc := Spec.Rsa.recoverPrimesApi.doc
      (notes := ["`vg_rsa_recover_primes`'s code, with `vg_rsa_public_precomputed_adx`'s Montgomery \
        multiplication."])
    code := Impl.Rsa.X86_64.Keys.Recover.code Proof.Bignum.X86_64.Mont.adx.mm
    contract := Spec.Rsa.recoverPrimesContract X86_64.abi
    verified := Proof.Rsa.X86_64.rp_verified _ (by decide +kernel)
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Rsa.X86_64
