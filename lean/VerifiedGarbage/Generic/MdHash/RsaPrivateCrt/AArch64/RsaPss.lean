module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees

/-! # RSASSA-PSS signing on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (privOf)
open VG.Proof.RsaPss.AArch64 (encOf)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("crt", c.suffix)]
    code := Impl.RsaPss.AArch64.signC (encOf v).name (encOf v).code (privOf c).name (privOf c).code
    stack := stk (privOf c).stack
    verified := Proof.RsaPss.AArch64.sign_verified v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPss
