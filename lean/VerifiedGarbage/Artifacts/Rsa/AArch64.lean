import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Rsa.AArch64.PubChecked
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified

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
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Rsa.AArch64
