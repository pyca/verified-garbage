module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Inst
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSASSA-PSS with SHA-1 on PPC64LE: verification and signing -/

@[expose] public section

namespace VG.Artifacts.RsaPssSha1.PPC64LE

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha1 Spec.Mgf1.sha1).artifact PPC64LE.target {
    code := Impl.RsaPss.PPC64LE.verifyPrecomputed Proof.Hmac.Stream.PPC64LE.Sha1.hash
    stack := 304
    verified := Proof.RsaPss.PPC64LE.link_verified Proof.RsaPss.PPC64LE.sha1L },
  (Spec.RsaPss.signApi Spec.Mgf1.sha1 Spec.Mgf1.sha1).artifact PPC64LE.target {
    code := Impl.RsaPss.PPC64LE.Sign.sign Proof.Hmac.Stream.PPC64LE.Sha1.hash
    stack := 3776
    verified := Proof.RsaPss.PPC64LE.Sg.sign_link_verified Proof.RsaPss.PPC64LE.sha1L }]

end VG.Artifacts.RsaPssSha1.PPC64LE
