module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.Rust
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances

/-! # EMSA-PSS's encoding and its check on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.AArch64.RsaPss

open VG.Proof.RsaPss.AArch64 (encOf chkOf)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := [
  (Spec.RsaPss.encodeApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := v.suffix
    code := (encOf v).code
    stack := (encOf v).stack
    verified := (encOf v).verified
    features := v.features },
  (Spec.RsaPss.checkEncodingApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := v.suffix
    code := (chkOf v).code
    stack := (chkOf v).stack
    verified := (chkOf v).verified
    features := v.features }]

end VG.Generic.MdHash.AArch64.RsaPss
