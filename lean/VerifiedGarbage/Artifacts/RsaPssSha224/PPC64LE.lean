module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Inst
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS with SHA-224 on PPC64LE: verification and signing

Verification uses 304 bytes of stack: its frame (256 bytes) and the 48 bytes
below it that the hash functions' calls use; `vg_rsa_public_precomputed_checked`
uses none.

Signing uses 3776 bytes: the same frame, the 192 bytes of the frame from which
it calls `vg_rsa_private_checked` (which hold that function's stack arguments
and the 48 bytes the hash functions' calls use), and `vg_rsa_private_checked`'s
3328 bytes.
-/

@[expose] public section

namespace VG.Artifacts.RsaPssSha224.PPC64LE

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact PPC64LE.target {
    code := Impl.RsaPss.PPC64LE.verifyPrecomputed Proof.Hmac.Stream.PPC64LE.Sha224.hash
    stack := 304
    verified := Proof.RsaPss.PPC64LE.link_verified Proof.RsaPss.PPC64LE.sha224L },
  (Spec.RsaPss.signApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact PPC64LE.target {
    code := Impl.RsaPss.PPC64LE.Sign.sign Proof.Hmac.Stream.PPC64LE.Sha224.hash
    stack := 3776
    verified := Proof.RsaPss.PPC64LE.Sg.sign_link_verified Proof.RsaPss.PPC64LE.sha224L }]

end VG.Artifacts.RsaPssSha224.PPC64LE
