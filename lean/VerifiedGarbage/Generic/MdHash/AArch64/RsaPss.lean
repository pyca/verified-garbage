module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.Rust
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances

/-!
# EMSA-PSS's encoding and its check on AArch64

A generic file (see `TCB/Emit.lean`): `vg_rsa_pss_<H>_mgf1_<H>_encode` and
`vg_rsa_pss_<H>_mgf1_<H>_check_encoding`, for the hash function of an
`MdHash` variant `v` with MGF1 over the same hash function, calling `v`'s
compression function, are emitted once for each variant, named with its
suffix (e.g. `vg_rsa_pss_sha256_mgf1_sha256_encode_sha2`). RSASSA-PSS's
signing and verification call them (`Generic/MdHash/RsaPrivateCrt/AArch64/RsaPss.lean`,
`Generic/MdHash/RsaPublicPrecomputed/AArch64/RsaPss.lean`).

Each one's stack is its frame and 16 bytes below it, for the hash
function's `init` (its compression function has no frame).
-/

@[expose] public section

namespace VG.Generic.MdHash.AArch64.RsaPss

open VG.Proof.RsaPss.AArch64 (encOf chkOf)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := [
  (Spec.RsaPss.encodeApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := v.suffix
    code := (encOf v).code
    stack := (encOf v).stack
    verified := (encOf v).verified
    features := v.features },
  (Spec.RsaPss.checkEncodingApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := v.suffix
    code := (chkOf v).code
    stack := (chkOf v).stack
    verified := (chkOf v).verified
    features := v.features }]

end VG.Generic.MdHash.AArch64.RsaPss
