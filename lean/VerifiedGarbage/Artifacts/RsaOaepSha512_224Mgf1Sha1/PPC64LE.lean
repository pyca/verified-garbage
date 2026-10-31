module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Inst
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-OAEP with SHA-512/224 and MGF1 with SHA-1 on PPC64LE: encryption and decryption

Encryption uses 304 bytes of stack: its frame (256 bytes) and the 48 bytes below it
that the hash functions' calls use; `vg_rsa_public_precomputed_checked` uses
none.

Decryption uses 3776 bytes: the same frame, the 192 bytes of the frame from
which it calls `vg_rsa_private_checked` (which hold that function's stack
arguments and the 48 bytes the hash functions' calls use), and
`vg_rsa_private_checked`'s 3328 bytes.
-/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha512_224Mgf1Sha1.PPC64LE

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha1).artifact PPC64LE.target {
    code := Impl.RsaOaep.PPC64LE.encrypt Proof.Hmac.Stream.PPC64LE.Sha512_224.hash Proof.Hmac.Stream.PPC64LE.Sha1.hash
    stack := 304
    verified := Proof.RsaOaep.PPC64LE.link_verified Proof.RsaOaep.PPC64LE.sha512_224L Proof.RsaOaep.PPC64LE.sha1L },
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha1).artifact PPC64LE.target {
    code := Impl.RsaOaep.PPC64LE.Dec.decrypt Proof.Hmac.Stream.PPC64LE.Sha512_224.hash
      Proof.Hmac.Stream.PPC64LE.Sha1.hash
    stack := 3776
    verified := Proof.RsaOaep.PPC64LE.Dec.dec_link_verified Proof.RsaOaep.PPC64LE.sha512_224L
      Proof.RsaOaep.PPC64LE.sha1L }]

end VG.Artifacts.RsaOaepSha512_224Mgf1Sha1.PPC64LE
