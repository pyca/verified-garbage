module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS verification with SHA-256 on PPC64LE

It uses 304 bytes of stack: its frame (256 bytes) and the 48 bytes below it
that the hash functions' calls use; `vg_rsa_public_precomputed_checked` uses
none.
-/

@[expose] public section

namespace VG.Artifacts.RsaPssSha256.PPC64LE

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha256 Spec.Mgf1.sha256).artifact PPC64LE.target {
    notes := ["This implementation calls `vg_rsa_public_precomputed_checked` with the cached modulus \
      values, then checks EMSA-PSS in its working space without branching on the encoding: `maskedDB` \
      is unmasked with MGF1 calling `" ++ Proof.Hmac.Stream.PPC64LE.Sha256.hash.updN ++ "`, and the end of \
      `DB`'s padding is found by a scan of all its bytes. A specified salt length copies that many \
      trailing bytes of `DB` into `M'` and hashes them; an unknown salt length shifts `DB` into place in \
      ten masked passes and finalizes a copy of the hash state at every length of `M'`, keeping the \
      digest at the salt's. Only the lengths, the salt-length mode and the public key decide a branch \
      or an address."]
    code := Impl.RsaPss.PPC64LE.verifyPrecomputed Proof.Hmac.Stream.PPC64LE.Sha256.hash
    stack := 304
    verified := Proof.RsaPss.PPC64LE.link_verified Proof.RsaPss.PPC64LE.sha256L }]

end VG.Artifacts.RsaPssSha256.PPC64LE
