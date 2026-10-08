import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Verified
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Verified
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Calls

/-! # RSA key generation (FIPS 186-5 A.1.3) on x86-64 -/

namespace VG.Artifacts.RsaKeyGen.X86_64

def artifacts : List Artifact := [
  { Spec.RsaKeyGen.candidateApi with
    target := X86_64.target
    doc := Spec.RsaKeyGen.candidateApi.doc
      (notes := ["Baseline x86-64: `|c − p|` by a subtraction and a masked negation; trial division \
        by Montgomery reduction of `c`'s 32-bit halves modulo each small prime, the masks of all \
        primes or'ed; `gcd(c − 1, e)` by `(c − 1) mod e` bit by bit and 128 steps of a binary gcd \
        with masks; and Miller–Rabin with `vg_rsa_public`'s Montgomery multiplication (by calls of \
        `vg_rsa_mont_mul`), a \
        witness outside `[2, c − 2]` given bit 1 and cleared its top bit by masks, and each \
        exponentiated over all the bits of `c − 1` but the lowest, a square per bit and the \
        factor chosen by the bit's mask, with the flag of a passing witness kept by masks. The \
        code branches only on what the leak allows: the result of each check, and whether each \
        witness passed."])
    code := Impl.RsaKeyGen.X86_64.Candidate.code Proof.Rsa.X86_64.CallMont.base.mm
    contract := Spec.RsaKeyGen.candidateContract X86_64.abi 8
    stack := 8
    verified := Proof.RsaKeyGen.X86_64.candidate_call_verified Proof.Bignum.X86_64.Mont.fnBase (by decide +kernel)
      rfl (by decide +kernel)
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.RsaKeyGen.candidateApi with
    target := X86_64.target
    name := Spec.RsaKeyGen.candidateApi.name ++ "_adx"
    doc := Spec.RsaKeyGen.candidateApi.doc
      (notes := ["`vg_rsa_keygen_candidate`'s code, with Montgomery multiplication by calls of \
        `vg_rsa_mont_mul_adx`."])
    code := Impl.RsaKeyGen.X86_64.Candidate.code Proof.Rsa.X86_64.CallMont.adx.mm
    contract := Spec.RsaKeyGen.candidateContract X86_64.abi 8
    stack := 8
    verified := Proof.RsaKeyGen.X86_64.candidate_call_verified Proof.Bignum.X86_64.Mont.fnAdx (by decide +kernel)
      rfl (by decide +kernel)
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.RsaKeyGen.keyApi with
    target := X86_64.target
    doc := Spec.RsaKeyGen.keyApi.doc
      (notes := ["Baseline x86-64, on `vg_rsa_public`'s working space and the RSA key routines' \
        constant-time arithmetic: `p` and `q` swapped under the mask of `p < q`; \
        `lcm(p − 1, q − 1)` as `(p − 1)(q − 1)` divided by `gcd(p − 1, q − 1)`, its power of two \
        found by `64 W` halving steps under masks and its odd part by the binary extended \
        Euclidean algorithm; `d` by the inverse of `L mod e` modulo `e` for an odd `e` (then \
        `d = Q (e − x) + (1 + R (e − x)) / e`), or of `e mod L` modulo `L` for an even one; \
        `qInv`, `dP` and `dQ` by the inverse and the division; the checks as masks, the outputs \
        stored under the final one. The code branches only on `e` and on whether `d` is too \
        small (the status 2)."])
    code := Impl.RsaKeyGen.X86_64.Key.code
    contract := Spec.RsaKeyGen.keyContract X86_64.abi
    verified := Proof.RsaKeyGen.X86_64.Key.key_verified (by decide +kernel)
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.RsaKeyGen.X86_64
