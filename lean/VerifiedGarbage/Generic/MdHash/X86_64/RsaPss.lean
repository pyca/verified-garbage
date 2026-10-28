module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.RsaPss.X86_64.Instances
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCt
public import VerifiedGarbage.Proof.Sha256.X86_64.Lit

/-!
# EMSA-PSS's encoding and its check on x86-64

A generic file (see `TCB/Emit.lean`): `vg_rsa_pss_<H>_mgf1_<H>_encode` and
`vg_rsa_pss_<H>_mgf1_<H>_check_encoding`, for the hash function of an
`MdHash` variant `v` with MGF1 over the same hash function, calling `v`'s
compression function, are emitted once for each variant, named with its
suffix (e.g. `vg_rsa_pss_sha256_mgf1_sha256_encode_shani`). RSASSA-PSS's
signing and verification call them (`Generic/MdHash/RsaPrivateCrt/X86_64/RsaPss.lean`,
`Generic/MdHash/RsaPublicPrecomputed/X86_64/RsaPss.lean`).

Each one's stack is its frame and a return address: its calls use none.
-/

@[expose] public section

namespace VG.Generic.MdHash.X86_64.RsaPss

open VG.Proof.RsaPss.X86_64 (encStack chkStack encOf chkOf)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := [
  (Spec.RsaPss.encodeApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation builds the encoding in its working space: `M'` is hashed over \
      the blocks its length needs and `DB` is masked with MGF1, then the encoding is copied to \
      `em`. Only the lengths decide a branch or an address."]
    code := (encOf v).code
    stack := encStack
    verified := Proof.RsaPss.X86_64.Enc.enc_verified v.ok v.K v.mgf v.pss
    spSafe := Code.all_of_allInstrs (encOf v).spSafe
    features := v.features },
  (Spec.RsaPss.checkEncodingApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation copies the encoding to its working space, unmasks `DB` with \
      MGF1 and checks every byte without branching on it: the position of `0x01` and the salt \
      are found by a scan over all of `DB`. Only the lengths decide a branch or an address."]
    code := (chkOf v).code
    stack := chkStack
    verified := Proof.RsaPss.X86_64.Chk.chk_verified v.ok v.K v.mgf v.pss
    spSafe := Code.all_of_allInstrs (chkOf v).spSafe
    features := v.features }]

end VG.Generic.MdHash.X86_64.RsaPss
