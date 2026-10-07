import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection on AArch64

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pkcs1_decrypt` calls SHA-256's streaming functions and
HMAC-SHA-256's `init` and `finalize`, made with the SHA-256 compression
function of an `MdHash` variant `v` (other hash functions emit nothing
here), and `vg_rsa_private_checked` calling an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/AArch64/`). It is emitted once
for each pair, named by `Emit.qualifiedName` with the tags `sha256` and
`crt` (e.g. `vg_rsa_pkcs1_decrypt_sha256_sha2`), and needs both's CPU
features.

Its stack is its frames, 224 bytes, and `vg_rsa_private_checked`'s 3248
bytes, which are more than the hash functions use.
-/

namespace VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPkcs1Enc

open VG.Proof.RsaPkcs1Enc.AArch64 (privOf dec_sat)
open VG.Proof.RsaPkcs1Enc.AArch64.Dec (HH decStack dec_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact :=
  match v.sha256 with
  | none => []
  | some h => [
    { Spec.RsaPkcs1Enc.decryptApi with
      name := Emit.qualifiedName Spec.RsaPkcs1Enc.decryptApi.name [("sha256", h.suffix), ("crt", c.suffix)]
      target := AArch64.target
      doc := Spec.RsaPkcs1Enc.decryptApi.doc
        (notes := ["This implementation calls `" ++ (privOf c).name ++ "`, then derives `KDK` and \
          the alternative message and lengths with `" ++ (HH h).updN ++ "`, `" ++ (HH h).hmacInitN ++
          "` and `" ++ (HH h).hmacFinN ++ "`, a block of IRPRF per HMAC. The padding's checks, the \
          scan for the separator, the choice of the alternative length and of the message are masks \
          computed without branches, and every byte of `EM` and of the alternative message is read \
          whichever is returned."])
      code := Impl.RsaPkcs1Enc.AArch64.Decrypt.code (HH h) (privOf c).name (privOf c).code
      contract := Spec.RsaPkcs1Enc.decryptContract AArch64.abi (decStack (privOf c))
      stack := decStack (privOf c)
      verified := dec_verified h (privOf c) (dec_sat c)
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := h.features ++ c.features.filter (!h.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPkcs1Enc
