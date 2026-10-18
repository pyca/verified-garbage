module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecPcCT5
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection on x86-64

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pkcs1_decrypt_precomputed` calls SHA-256's streaming functions and
HMAC-SHA-256's `init` and `finalize`, made with the SHA-256 compression
function of an `MdHash` variant `v` (other hash functions emit nothing
here), and `vg_rsa_private_checked_precomputed` calling an implementation
`c` of `vg_rsa_private_crt_precomputed` (`Variants/RsaPrivateCrt/X86_64/`).
It is emitted once for each pair, named by `Emit.qualifiedName` with the
tags `sha256` and `crt` (e.g.
`vg_rsa_pkcs1_decrypt_precomputed_sha256_shani_crt_adx`), and needs both's
CPU features. The Rust code decrypts with it on x86-64, so
`vg_rsa_pkcs1_decrypt` is not emitted here.

Its stack is its frame, a return address and
`vg_rsa_private_checked_precomputed`'s 1208 bytes, which are more than the
hash functions use.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPkcs1Enc

open VG.Proof.RsaPkcs1Enc.X86_64.DecPc (HH privOf decStack dec_verified dec_spSafe)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact :=
  match v.sha256 with
  | none => []
  | some h => [
    Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact X86_64.target {
      suffix := Emit.qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
      notes := ["This implementation calls `" ++ (privOf c).name ++ "`, then derives `KDK` and \
          the alternative message and lengths with `" ++ (HH h).updN ++ "`, `" ++ (HH h).hmacInitN ++
          "` and `" ++ (HH h).hmacFinN ++ "`, a block of IRPRF per HMAC. The padding's checks, the \
          scan for the separator, the choice of the alternative length and of the message are masks \
          computed without branches, and every byte of `EM` and of the alternative message is read \
          whichever is returned."]
      code := Impl.RsaPkcs1Enc.X86_64.DecryptPc.code (HH h) (privOf c).name (privOf c).code
      stack := decStack
      verified := dec_verified h (privOf c)
      spSafe := dec_spSafe h (privOf c)
      features := h.features ++ c.features.filter (!h.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPkcs1Enc
