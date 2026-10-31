module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtx
public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import VerifiedGarbage.Proof.RsaPss.X86_64.PcCCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.PcCVerified
public import VerifiedGarbage.Proof.RsaPss.X86_64.Instances

/-!
# RSASSA-PSS verification using cached public-key values

Every hash compression variant combines with every precomputed RSA public
operation variant. The digest, signature and recovered encoding stay secret.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPublicPrecomputed.X86_64.RsaPss

open VG.Proof.RsaPss.X86_64 (verifyStack chkOf)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.PublicImpl) : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("rsa", c.suffix)]
    code := Impl.RsaPss.X86_64.verifyC (chkOf v).name (chkOf v).code c.name c.code
    stack := verifyStack
    verified := Proof.RsaPss.X86_64.Pc.codeC_verified (hvK := (chkOf v).ok) (hctK := (chkOf v).ct)
      (hdK := (chkOf v).depth) v.H v.mgf.mem (X86_64.SpSafe.of_all (Code.all_of_allInstrs (chkOf v).spSafe)) c
    spSafe := Code.all_of_allInstrs (Proof.RsaPss.X86_64.Pc.codeC_spAll
      (X86_64.SpSafe.of_all (Code.all_of_allInstrs (chkOf v).spSafe)) c)
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPublicPrecomputed.X86_64.RsaPss
