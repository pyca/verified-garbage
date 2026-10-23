module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreVerified
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
    verified := Proof.Bignum.PPC64LE.Pre.precompute_verified }]

end VG.Artifacts.Rsa.PPC64LE
