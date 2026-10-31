module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.RsaPss.X86_64.Instances
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCt
public import VerifiedGarbage.Proof.Sha256.X86_64.Lit

/-! # EMSA-PSS's encoding and its check on x86-64 -/

@[expose] public section

namespace VG.Generic.MdHash.X86_64.RsaPss

open VG.Proof.RsaPss.X86_64 (encStack chkStack encOf chkOf)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := [
  (Spec.RsaPss.encodeApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := v.suffix
    code := (encOf v).code
    stack := encStack
    verified := Proof.RsaPss.X86_64.Enc.enc_verified v.ok v.K v.mgf v.pss
    spSafe := Code.all_of_allInstrs (encOf v).spSafe
    features := v.features },
  (Spec.RsaPss.checkEncodingApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := v.suffix
    code := (chkOf v).code
    stack := chkStack
    verified := Proof.RsaPss.X86_64.Chk.chk_verified v.ok v.K v.mgf v.pss
    spSafe := Code.all_of_allInstrs (chkOf v).spSafe
    features := v.features }]

end VG.Generic.MdHash.X86_64.RsaPss
