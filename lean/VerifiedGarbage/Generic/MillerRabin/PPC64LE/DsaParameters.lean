module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Instances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA parameter generation on PPC64LE, calling the probable-prime tests over each Miller–Rabin round -/

@[expose] public section

namespace VG.Generic.MillerRabin.PPC64LE.DsaParameters
open VG Proof.Dsa.PPC64LE.Gen

def artifacts (v : Proof.MillerRabin.PPC64LE.RoundImpl) : List Artifact := [
  Spec.Dsa.generateParametersApi.artifact PPC64LE.target {
    suffix := v.suffix
    notes := ["The complete bounded parameter search runs in verified code: seed hashing by calls \
        of `vg_sha1_compress` or `vg_sha256_compress` on one padded block, q and p built in the key \
        working space of the RSA key routines in `scratch`, the probable-prime tests of each size \
        over the same Miller–Rabin round, `g` by RSA's fixed-window power in the P space, the domain \
        check of `vg_dsa_check_parameters`, and the output copied or zeroed. The search's state is \
        kept in a header of `scratch`, whose address stays in `r28`. The three input tapes are public \
        under the contract. Only 1024/160, 2048/256 and 3072/256 are generated."]
    code := Impl.Dsa.PPC64LE.Generation.code (gen1 v) (gen2 v) (gen3 v)
    stack := 176
    consts := Impl.RsaKeyGen.TrialTable32.consts
    verified := generate_params v
    features := v.features }]

end VG.Generic.MillerRabin.PPC64LE.DsaParameters
