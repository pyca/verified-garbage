module

public import VerifiedGarbage.Proof.RsaPss.X86.VfVerified
public import VerifiedGarbage.Proof.RsaPss.X86.VfSat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Md5

/-! # RSASSA-PSS verification with MD5 on x86 -/

@[expose] public section

namespace VG.Artifacts.RsaPssMd5.X86

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.md5 Spec.Mgf1.md5).artifact X86.target {
    code := Proof.RsaPss.X86.Vf.verifyCode Proof.RsaPss.X86.md5 Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaPss.X86.Vf.stackBytes
    verified := Proof.RsaPss.X86.Vf.verify_verified Proof.RsaPss.X86.md5 Proof.RsaPss.X86.Vf.verify_sat_md5
      Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaPss.X86.Vf.code_sp Proof.RsaPss.X86.md5 Proof.RsaPkcs1Sig.X86.Ver.baseline }]

end VG.Artifacts.RsaPssMd5.X86
