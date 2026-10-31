module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha224

/-! # RSASSA-PSS signing with SHA-224 on x86, for each SHA-256 backend and implementation of the CRT -/

@[expose] public section

namespace VG.Generic.Sha256.RsaPrivateCrt.X86.RsaPssSha224

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (c : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]
    code := Proof.RsaPss.X86.Sg.signCode (Proof.RsaPss.X86.sha224 v) c
    stack := Proof.RsaPss.X86.Sg.stackBytes
    verified := Proof.RsaPss.X86.Sg.sign_verified (Proof.RsaPss.X86.sha224 v) Proof.RsaPss.X86.Sg.sign_sat_sha224 c
    spSafe := Proof.RsaPss.X86.Sg.code_sp (Proof.RsaPss.X86.sha224 v) c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Sha256.RsaPrivateCrt.X86.RsaPssSha224
