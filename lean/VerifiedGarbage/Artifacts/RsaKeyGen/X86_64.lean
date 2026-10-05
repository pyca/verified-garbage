import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Verified
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

/-! # RSA key generation (FIPS 186-5 A.1.3) on x86-64 -/

namespace VG.Artifacts.RsaKeyGen.X86_64

def artifacts : List Artifact := [
  { Spec.RsaKeyGen.candidateApi with
    target := X86_64.target
    doc := Spec.RsaKeyGen.candidateApi.doc
      (notes := ["Baseline x86-64: `|c − p|` by a subtraction and a masked negation; trial division \
        by Montgomery reduction of `c`'s 32-bit halves modulo each small prime, the masks of all \
        primes or'ed; `gcd(c − 1, e)` by `(c − 1) mod e` bit by bit and 128 steps of a binary gcd \
        with masks; and Miller–Rabin with `vg_rsa_public`'s Montgomery multiplication, a \
        witness outside `[2, c − 2]` given bit 1 and cleared its top bit by masks, and each \
        exponentiated over all the bits of `c − 1` but the lowest, a square per bit and the \
        factor chosen by the bit's mask, with the flag of a passing witness kept by masks. The \
        code branches only on what the leak allows: the result of each check, and whether each \
        witness passed."])
    code := Impl.RsaKeyGen.X86_64.Candidate.code Proof.Bignum.X86_64.Mont.base.mm
    contract := Spec.RsaKeyGen.candidateContract X86_64.abi
    verified := Proof.RsaKeyGen.X86_64.candidate_verified _ (by decide +kernel)
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.RsaKeyGen.candidateApi with
    target := X86_64.target
    name := Spec.RsaKeyGen.candidateApi.name ++ "_adx"
    doc := Spec.RsaKeyGen.candidateApi.doc
      (notes := ["`vg_rsa_keygen_candidate`'s code, with `vg_rsa_public_precomputed_adx`'s \
        Montgomery multiplication."])
    code := Impl.RsaKeyGen.X86_64.Candidate.code Proof.Bignum.X86_64.Mont.adx.mm
    contract := Spec.RsaKeyGen.candidateContract X86_64.abi
    verified := Proof.RsaKeyGen.X86_64.candidate_verified _ (by decide +kernel)
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.RsaKeyGen.X86_64
