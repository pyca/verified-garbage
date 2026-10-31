module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Inst
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-OAEP with SHA-512/224 and MGF1 with SHA-512/224 on PPC64LE: encryption and decryption -/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha512_224Mgf1Sha512_224.PPC64LE

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha512_224).artifact PPC64LE.target {
    code := Impl.RsaOaep.PPC64LE.encrypt Proof.Hmac.Stream.PPC64LE.Sha512_224.hash Proof.Hmac.Stream.PPC64LE.Sha512_224.hash
    stack := 304
    verified := Proof.RsaOaep.PPC64LE.link_verified Proof.RsaOaep.PPC64LE.sha512_224L Proof.RsaOaep.PPC64LE.sha512_224L },
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha512_224).artifact PPC64LE.target {
    code := Impl.RsaOaep.PPC64LE.Dec.decrypt Proof.Hmac.Stream.PPC64LE.Sha512_224.hash
      Proof.Hmac.Stream.PPC64LE.Sha512_224.hash
    stack := 3776
    verified := Proof.RsaOaep.PPC64LE.Dec.dec_link_verified Proof.RsaOaep.PPC64LE.sha512_224L
      Proof.RsaOaep.PPC64LE.sha512_224L }]

end VG.Artifacts.RsaOaepSha512_224Mgf1Sha512_224.PPC64LE
