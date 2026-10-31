module

public import VerifiedGarbage.Proof.RsaPss.X86.VfVerified
public import VerifiedGarbage.Proof.RsaPss.X86.VfSat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha256

/-! # RSASSA-PSS verification with SHA-256 on x86, for each SHA-256 backend -/

@[expose] public section

namespace VG.Generic.Sha256.X86.RsaPssSha256

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha256 Spec.Mgf1.sha256).artifact X86.target {
    suffix := v.stream.suffix
    code := Proof.RsaPss.X86.Vf.verifyCode (Proof.RsaPss.X86.sha256 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaPss.X86.Vf.stackBytes
    verified := Proof.RsaPss.X86.Vf.verify_verified (Proof.RsaPss.X86.sha256 v) Proof.RsaPss.X86.Vf.verify_sat_sha256
      Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaPss.X86.Vf.code_sp (Proof.RsaPss.X86.sha256 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    features := v.features }]

end VG.Generic.Sha256.X86.RsaPssSha256
