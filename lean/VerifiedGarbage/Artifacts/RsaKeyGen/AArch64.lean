module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.Rsa.AArch64.CvCT
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTBase

/-! # RSA key generation (FIPS 186-5 A.1.3) on AArch64 -/

@[expose] public section

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
        and each exponentiated by `E = (c − 1) / 2^σ` (`σ ∈ [1, 4]`, `σ` congruent to the exponent of \
        2 in `c − 1` mod 4, so that `E`'s lowest set bit ends a window; `E` by halvings under masks \
        from the lowest set bit of `c − 1`) in fixed windows of 4 bits: four squarings, the table \
        entry of the window's digit selected from all 16 powers of the witness under the masks of \
        each entry's index against the digit, and a multiplication; then three more squarings. The \
        flag of a passing witness is kept by masks: or'ed with `y = −1` after each squaring (under the \
        masks of the last three's count), and reset to `y = ±1` after a nonzero digit. The code \
        branches only on what the leak allows: the result of each check, and whether each witness \
        passed."])
    code := Impl.RsaKeyGen.AArch64.Candidate.code Proof.Bignum.AArch64.Mont.base.mm
    contract := Spec.RsaKeyGen.candidateContract AArch64.abi
    verified := Proof.RsaKeyGen.AArch64.candidate_verified _
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.RsaKeyGen.keyApi with
    target := AArch64.target
    doc := Spec.RsaKeyGen.keyApi.doc
      (notes := ["Baseline AArch64, on the working space of the RSA key routines and their constant-time \
        arithmetic: `p` and `q` swapped under the mask of `p < q`; `lcm(p − 1, q − 1)` as \
        `(p − 1)(q − 1)` divided by `gcd(p − 1, q − 1)`, its power of two found by `64 W` halving \
        steps under masks and its odd part by the binary extended Euclidean algorithm; `d` by the \
        inverse of `L mod e` modulo `e` for an odd `e` (then `d = Q (e − x) + (1 + R (e − x)) / e`), \
        or of `e mod L` modulo `L` for an even one; `qInv`, `dP` and `dQ` by the inverse and the \
        division; the checks as masks, the outputs stored under the final one. The code branches \
        only on `e` and on whether `d` is too small (the status 2)."])
    code := Impl.RsaKeyGen.AArch64.Key.code
    contract := Spec.RsaKeyGen.keyContract AArch64.abi
    verified := Proof.RsaKeyGen.AArch64.Key.key_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.RsaKeyGen.AArch64
