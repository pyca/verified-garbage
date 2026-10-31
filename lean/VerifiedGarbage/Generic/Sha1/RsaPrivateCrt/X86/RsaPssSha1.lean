module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha1

/-! # RSASSA-PSS signing with SHA-1 on x86, for each SHA-1 backend and implementation of the CRT -/

@[expose] public section

namespace VG.Generic.Sha1.RsaPrivateCrt.X86.RsaPssSha1

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Proof.Sha1.X86.Variants.Backend) (c : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha1 Spec.Mgf1.sha1).artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha1", v.stream.suffix), ("crt", c.suffix)]
    code := Proof.RsaPss.X86.Sg.signCode (Proof.RsaPss.X86.sha1 v) c
    stack := Proof.RsaPss.X86.Sg.stackBytes
    verified := Proof.RsaPss.X86.Sg.sign_verified (Proof.RsaPss.X86.sha1 v) Proof.RsaPss.X86.Sg.sign_sat_sha1 c
    spSafe := Proof.RsaPss.X86.Sg.code_sp (Proof.RsaPss.X86.sha1 v) c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Sha1.RsaPrivateCrt.X86.RsaPssSha1
