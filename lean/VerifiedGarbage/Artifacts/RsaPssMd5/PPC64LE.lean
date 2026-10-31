module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Inst
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSASSA-PSS with MD5 on PPC64LE: verification and signing -/

@[expose] public section

namespace VG.Artifacts.RsaPssMd5.PPC64LE

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.md5 Spec.Mgf1.md5).artifact PPC64LE.target {
    code := Impl.RsaPss.PPC64LE.verifyPrecomputed Proof.Hmac.Stream.PPC64LE.Md5.hash
    stack := 304
    verified := Proof.RsaPss.PPC64LE.link_verified Proof.RsaPss.PPC64LE.md5L },
  (Spec.RsaPss.signApi Spec.Mgf1.md5 Spec.Mgf1.md5).artifact PPC64LE.target {
    code := Impl.RsaPss.PPC64LE.Sign.sign Proof.Hmac.Stream.PPC64LE.Md5.hash
    stack := 3776
    verified := Proof.RsaPss.PPC64LE.Sg.sign_link_verified Proof.RsaPss.PPC64LE.md5L }]

end VG.Artifacts.RsaPssMd5.PPC64LE
