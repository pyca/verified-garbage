module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-OAEP with SHA-512/256 and MGF1 with SHA-512/256 on PPC64LE: encryption

It uses 304 bytes of stack: its frame (256 bytes) and the 48 bytes below it
that the hash functions' calls use; `vg_rsa_public_precomputed_checked` uses
none.
-/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha512_256Mgf1Sha512_256.PPC64LE

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha512_256 Spec.Mgf1.sha512_256).artifact PPC64LE.target {
    notes := ["This implementation hashes the label with `" ++ Proof.Hmac.Stream.PPC64LE.Sha512_256.hash.updN ++
      "`, masks `DB` and the seed with MGF1 calling `" ++ Proof.Hmac.Stream.PPC64LE.Sha512_256.hash.updN ++
      "`, and calls `vg_rsa_public_precomputed_checked` with the cached modulus values. The message's \
      length is public; its bytes, the label's and the seed's are only copied, hashed and masked."]
    code := Impl.RsaOaep.PPC64LE.encrypt Proof.Hmac.Stream.PPC64LE.Sha512_256.hash Proof.Hmac.Stream.PPC64LE.Sha512_256.hash
    stack := 304
    verified := Proof.RsaOaep.PPC64LE.link_verified Proof.RsaOaep.PPC64LE.sha512_256L Proof.RsaOaep.PPC64LE.sha512_256L }]

end VG.Artifacts.RsaOaepSha512_256Mgf1Sha512_256.PPC64LE
