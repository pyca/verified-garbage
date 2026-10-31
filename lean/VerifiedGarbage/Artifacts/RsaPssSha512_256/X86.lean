module

public import VerifiedGarbage.Proof.RsaPss.X86.VfVerified
public import VerifiedGarbage.Proof.RsaPss.X86.VfSat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha512

/-! # RSASSA-PSS verification with SHA-512/256 on x86 -/

@[expose] public section

namespace VG.Artifacts.RsaPssSha512_256.X86

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha512_256 Spec.Mgf1.sha512_256).artifact X86.target {
    code := Proof.RsaPss.X86.Vf.verifyCode Proof.RsaPss.X86.sha512_256 Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaPss.X86.Vf.stackBytes
    verified := Proof.RsaPss.X86.Vf.verify_verified Proof.RsaPss.X86.sha512_256 Proof.RsaPss.X86.Vf.verify_sat_sha512_256
      Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaPss.X86.Vf.code_sp Proof.RsaPss.X86.sha512_256 Proof.RsaPkcs1Sig.X86.Ver.baseline }]

end VG.Artifacts.RsaPssSha512_256.X86
