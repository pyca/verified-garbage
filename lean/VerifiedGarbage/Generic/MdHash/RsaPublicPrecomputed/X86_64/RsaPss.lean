module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtx
public import VerifiedGarbage.Spec.RsaPss.Precomputed
import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCT

/-!
# RSASSA-PSS verification using cached public-key values

Every hash compression variant combines with every precomputed RSA public
operation variant. The digest, signature and recovered encoding stay secret.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPublicPrecomputed.X86_64.RsaPss

open VG.Proof.RsaPss.X86_64 (verifyStack)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.PublicImpl) : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("rsa", c.suffix)]
    notes := ["This implementation calls `" ++ c.name ++ "` with the cached public-key values, \
        then checks EMSA-PSS using the same padding and hashing code as the original verifier."]
    code := Impl.RsaPss.X86_64.Precomputed.code v.H c.name c.code
    stack := verifyStack
    verified := Proof.RsaPss.X86_64.Pc.verified c v.ok v.K v.mgf v.pss
    spSafe := Proof.RsaPss.X86_64.Pc.code_spSafe v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPublicPrecomputed.X86_64.RsaPss
