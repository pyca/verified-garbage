module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT5
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
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
`vg_rsa_pkcs1_decrypt` calls SHA-256's streaming functions and
HMAC-SHA-256's `init` and `finalize`, made with the SHA-256 compression
function of an `MdHash` variant `v` (other hash functions emit nothing
here), and `vg_rsa_private_checked` calling an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86_64/`). It is emitted once
for each pair, named by `Emit.qualifiedName` with the tags `sha256` and
`crt` (e.g. `vg_rsa_pkcs1_decrypt_sha256_shani_crt_adx`), and needs both's
CPU features.

Its stack is its frame, a return address and `vg_rsa_private_checked`'s
3256 bytes, which are more than the hash functions use.
`vg_rsa_pkcs1_decrypt_precomputed`, calling
`vg_rsa_private_checked_precomputed` (1208 bytes, still more), is emitted
the same way, with a frame 16 bytes larger for its callee's two more stack
arguments.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPkcs1Enc

open VG.Proof.RsaPkcs1Enc.X86_64 (privOf decStack)
open VG.Proof.RsaPkcs1Enc.X86_64.Dec (HH dec_verified dec_spSafe)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact :=
  match v.sha256 with
  | none => []
  | some h => [
    Spec.RsaPkcs1Enc.decryptApi.artifact X86_64.target {
      suffix := Emit.qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
      notes := ["This implementation calls `" ++ (privOf c).name ++ "`, then derives `KDK` and \
          the alternative message and lengths with `" ++ (HH h).updN ++ "`, `" ++ (HH h).hmacInitN ++
          "` and `" ++ (HH h).hmacFinN ++ "`, a block of IRPRF per HMAC. The padding's checks, the \
          scan for the separator, the choice of the alternative length and of the message are masks \
          computed without branches, and every byte of `EM` and of the alternative message is read \
          whichever is returned."]
      code := Impl.RsaPkcs1Enc.X86_64.Decrypt.code (HH h) (privOf c).name (privOf c).code
      stack := decStack
      verified := dec_verified h (privOf c)
      spSafe := dec_spSafe h (privOf c)
      features := h.features ++ c.features.filter (!h.features.contains ·) },
    Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact X86_64.target {
      suffix := Emit.qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
      notes := ["This implementation calls `" ++ (Proof.RsaPkcs1Enc.X86_64.DecPc.privOf c).name ++ "`, then \
          derives `KDK` and the alternative message and lengths with `" ++ (HH h).updN ++ "`, `" ++
          (HH h).hmacInitN ++ "` and `" ++ (HH h).hmacFinN ++ "`, a block of IRPRF per HMAC. The padding's \
          checks, the scan for the separator, the choice of the alternative length and of the message are \
          masks computed without branches, and every byte of `EM` and of the alternative message is read \
          whichever is returned."]
      code := Impl.RsaPkcs1Enc.X86_64.DecryptPc.code (Proof.RsaPkcs1Enc.X86_64.DecPc.HH h)
        (Proof.RsaPkcs1Enc.X86_64.DecPc.privOf c).name (Proof.RsaPkcs1Enc.X86_64.DecPc.privOf c).code
      stack := Proof.RsaPkcs1Enc.X86_64.DecPc.decStack
      verified := Proof.RsaPkcs1Enc.X86_64.DecPc.dec_verified h (Proof.RsaPkcs1Enc.X86_64.DecPc.privOf c)
      spSafe := Proof.RsaPkcs1Enc.X86_64.DecPc.dec_spSafe h (Proof.RsaPkcs1Enc.X86_64.DecPc.privOf c)
      features := h.features ++ c.features.filter (!h.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPkcs1Enc
