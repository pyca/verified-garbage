import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Verified

/-! # RSA key generation (FIPS 186-5 A.1.3) on AArch64 -/

namespace VG.Artifacts.RsaKeyGen.AArch64

def artifacts : List Artifact := [
  { Spec.RsaKeyGen.candidateApi with
    target := AArch64.target
    doc := Spec.RsaKeyGen.candidateApi.doc
      (notes := ["Baseline AArch64, on the working space of the RSA key routines: `|c − p|` by two \
        subtractions, the difference selected by the borrow's mask and compared with `2^(bits − 100)`; \
        trial division by Montgomery reduction of `c`'s 32-bit halves modulo each small prime, the \
        masks of all primes or'ed; `gcd(c − 1, e)` by `(c − 1) mod e` bit by bit and 128 steps of a \
        binary gcd with masks; and Miller–Rabin with `vg_rsa_public_checked`'s Montgomery \
        multiplication, a witness outside `[2, c − 2]` given bit 1 and cleared its top bit by masks, \
        and each exponentiated over all the bits of `c − 1` but the lowest, a square per bit and the \
        factor chosen by the bit's mask, with the flag of a passing witness kept by masks. The code \
        branches only on what the leak allows: the result of each check, and whether each witness \
        passed."])
    code := Impl.RsaKeyGen.AArch64.Candidate.code Proof.Bignum.AArch64.Mont.base.mm
    contract := Spec.RsaKeyGen.candidateContract AArch64.abi
    verified := Proof.RsaKeyGen.AArch64.candidate_verified _
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.RsaKeyGen.AArch64
