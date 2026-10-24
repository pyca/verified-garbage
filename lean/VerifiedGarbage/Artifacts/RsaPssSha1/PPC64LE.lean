module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Inst
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS with SHA-1 on PPC64LE: verification and signing

Verification uses 304 bytes of stack: its frame (256 bytes) and the 48 bytes
below it that the hash functions' calls use; `vg_rsa_public_precomputed_checked`
uses none.

Signing uses 3776 bytes: the same frame, the 192 bytes of the frame from which
it calls `vg_rsa_private_checked` (which hold that function's stack arguments
and the 48 bytes the hash functions' calls use), and `vg_rsa_private_checked`'s
3328 bytes.
-/

@[expose] public section

namespace VG.Artifacts.RsaPssSha1.PPC64LE

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha1 Spec.Mgf1.sha1).artifact PPC64LE.target {
    notes := ["This implementation calls `vg_rsa_public_precomputed_checked` with the cached modulus \
      values, then checks EMSA-PSS in its working space without branching on the encoding: `maskedDB` \
      is unmasked with MGF1 calling `" ++ Proof.Hmac.Stream.PPC64LE.Sha1.hash.updN ++ "`, and the end of \
      `DB`'s padding is found by a scan of all its bytes. A specified salt length copies that many \
      trailing bytes of `DB` into `M'` and hashes them; an unknown salt length shifts `DB` into place in \
      ten masked passes and finalizes a copy of the hash state at every length of `M'`, keeping the \
      digest at the salt's. Only the lengths, the salt-length mode and the public key decide a branch \
      or an address."]
    code := Impl.RsaPss.PPC64LE.verifyPrecomputed Proof.Hmac.Stream.PPC64LE.Sha1.hash
    stack := 304
    verified := Proof.RsaPss.PPC64LE.link_verified Proof.RsaPss.PPC64LE.sha1L },
  (Spec.RsaPss.signApi Spec.Mgf1.sha1 Spec.Mgf1.sha1).artifact PPC64LE.target {
    notes := ["This implementation hashes `M'` with `" ++ Proof.Hmac.Stream.PPC64LE.Sha1.hash.updN ++
      "`, masks `DB` with MGF1 calling `" ++ Proof.Hmac.Stream.PPC64LE.Sha1.hash.updN ++
      "`, and calls `vg_rsa_private_checked` on `EM`. The digest and the salt are only copied and \
      hashed; only the lengths, the modulus' first byte and the public key decide a branch or an \
      address."]
    code := Impl.RsaPss.PPC64LE.Sign.sign Proof.Hmac.Stream.PPC64LE.Sha1.hash
    stack := 3776
    verified := Proof.RsaPss.PPC64LE.Sg.sign_link_verified Proof.RsaPss.PPC64LE.sha1L }]

end VG.Artifacts.RsaPssSha1.PPC64LE
