module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreVerified
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubVerified
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
    verified := Proof.Bignum.PPC64LE.Pub.publicChecked_verified }]

end VG.Artifacts.Rsa.PPC64LE
