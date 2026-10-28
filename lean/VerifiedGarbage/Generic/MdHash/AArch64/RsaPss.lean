module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Emit
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
    notes := ["This implementation builds the encoding in its working space: `M'` is hashed over \
      the blocks its length needs and `DB` is masked with MGF1, then the encoding is copied to \
      `em`. Only the lengths decide a branch or an address."]
    code := (encOf v).code
    stack := (encOf v).stack
    verified := (encOf v).verified
    features := v.features },
  (Spec.RsaPss.checkEncodingApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation copies the encoding to its working space, unmasks `DB` with \
      MGF1 and checks every byte without branching on it: the position of `0x01` and the salt \
      are found by a scan over all of `DB`. A specified salt length copies that many trailing \
      bytes into `M'` and hashes only the blocks needed; an unknown salt length keeps the \
      oblivious shift and the maximum block count. Only the lengths and the salt-length mode \
      decide a branch or an address."]
    code := (chkOf v).code
    stack := (chkOf v).stack
    verified := (chkOf v).verified
    features := v.features }]

end VG.Generic.MdHash.AArch64.RsaPss
