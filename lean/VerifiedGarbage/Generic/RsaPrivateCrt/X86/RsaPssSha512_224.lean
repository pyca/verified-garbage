module

public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha512

/-! # RSASSA-PSS signing with SHA-512/224 on x86, for each implementation of the CRT -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86.RsaPssSha512_224

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (c : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha512_224).artifact X86.target {
    suffix := c.suffix
    code := Proof.RsaPss.X86.Sg.signCode Proof.RsaPss.X86.sha512_224 c
    stack := Proof.RsaPss.X86.Sg.stackBytes
    verified := Proof.RsaPss.X86.Sg.sign_verified Proof.RsaPss.X86.sha512_224 Proof.RsaPss.X86.Sg.sign_sat_sha512_224 c
    spSafe := Proof.RsaPss.X86.Sg.code_sp Proof.RsaPss.X86.sha512_224 c
    features := c.features }]

end VG.Generic.RsaPrivateCrt.X86.RsaPssSha512_224
