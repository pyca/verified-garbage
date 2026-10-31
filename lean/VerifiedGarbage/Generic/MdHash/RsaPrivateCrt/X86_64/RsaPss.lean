module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCVerified
public import VerifiedGarbage.Proof.RsaPss.X86_64.Instances

/-! # RSASSA-PSS signing on x86-64 -/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPss

open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)
open VG.Proof.RsaPss.X86_64 (signStack signC_verified signC_spAll encOf)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("crt", c.suffix)]
    code := Impl.RsaPss.X86_64.signC (encOf v).name (encOf v).code (privOf c).name (privOf c).code
    stack := signStack
    verified := signC_verified (hvE := (encOf v).ok) (hctE := (encOf v).ct)
      (hspE := X86_64.SpSafe.of_all (Code.all_of_allInstrs (encOf v).spSafe)) (hdE := (encOf v).depth)
      (hct := (privOf c).ct) (hdC := (privOf c).depth) v.H v.mgf.mem (privOf c).ok
      (X86_64.SpSafe.of_all (privOf c).spSafe)
    spSafe := Code.all_of_allInstrs (signC_spAll (X86_64.SpSafe.of_all (Code.all_of_allInstrs (encOf v).spSafe))
      (X86_64.SpSafe.of_all (privOf c).spSafe))
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPss
