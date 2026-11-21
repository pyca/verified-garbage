module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Scrub
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Fn
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86

/-! # RSA key generation (FIPS 186-5 A.1.3) on x86 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.X86

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact X86.target {
    code := Impl.RsaKeyGen.X86.Fn.generateInit
    verified := Proof.RsaKeyGen.X86.Scrub.generateInit_scrubbed }]

end VG.Artifacts.RsaKeyGen.X86

namespace VG.Artifacts.RsaKeyGen.X86

open VG VG.X86 VG.Proof.MillerRabin.X86

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.X86.variants.flatMap fun (v : RoundImpl) => [
    Spec.RsaKeyGen.keySearchApi.artifact target {
      suffix := v.suffix
      code := Impl.RsaKeyGen.X86.Fn.generate (Proof.RsaKeyGen.X86.Generate.srchOf v).call
        Proof.RsaKeyGen.X86.Generate.keyImpl.call
      verified := Proof.RsaKeyGen.X86.Scrub.generate_scrubbed v
      spSafe := Proof.RsaKeyGen.X86.Scrub.generate_spSafe v }])

end VG.Artifacts.RsaKeyGen.X86
