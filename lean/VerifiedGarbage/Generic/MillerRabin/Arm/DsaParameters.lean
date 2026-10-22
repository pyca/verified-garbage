module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Instances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA parameter generation on ARMv7, calling the probable-prime tests over each Miller–Rabin round -/

@[expose] public section

namespace VG.Generic.MillerRabin.Arm.DsaParameters
open VG Proof.Dsa.Arm.Gen

def artifacts (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact := [
  Spec.Dsa.generateParametersApi.artifact Arm.target {
    suffix := v.suffix
    notes := ["The complete bounded parameter search runs in verified code: seed \
        hashing by calls of `vg_sha1_compress` or `vg_sha256_compress` on one padded block, q and p \
        built in the key working space of the RSA key routines in `scratch`, the probable-prime \
        tests of each size over the same Miller–Rabin round, `g` by `vg_dsa_pow_{p_len/8}_{e}`, the \
        domain check of `vg_dsa_check_parameters`, and the output copied or zeroed. The three input \
        tapes are public under the contract. Only 1024/160, 2048/256 and 3072/256 are generated."]
    code := Impl.Dsa.Arm.Generation.code (geo1 v) (geo2 v) (geo3 v)
    stack := 304
    verified := params_verified v
    features := v.features }]

end VG.Generic.MillerRabin.Arm.DsaParameters
