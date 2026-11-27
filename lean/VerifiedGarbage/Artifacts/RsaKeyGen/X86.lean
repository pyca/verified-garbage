module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
import VerifiedGarbage.Proof.RsaKeyGen.X86.Scrub
import VerifiedGarbage.Impl.RsaKeyGen.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MillerRabin.X86.Backend
import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Verified
import VerifiedGarbage.Proof.Variants.MillerRabin.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSA key generation (FIPS 186-5 A.1.3) on x86 -/

namespace VG.Artifacts.RsaKeyGen.X86

def direct : List (Artifact X86.target) := [
  Spec.RsaKeyGen.keyInitApi.artifact X86.target {
    code := Impl.RsaKeyGen.X86.Fn.generateInit
    verified := Proof.RsaKeyGen.X86.Scrub.generateInit_scrubbed
    publicOutOk := Proof.RsaKeyGen.X86.Scrub.generateInit_public }]

end VG.Artifacts.RsaKeyGen.X86

namespace VG.Artifacts.RsaKeyGen.X86

open VG VG.X86 VG.Proof.MillerRabin.X86

public def artifacts : List (Artifact X86.target) :=
  direct ++
  (VG.Proof.Variants.MillerRabin.X86.variants.flatMap fun (v : RoundImpl) => [
    Spec.RsaKeyGen.keySearchApi.artifact target {
      suffix := v.suffix
      code := Impl.RsaKeyGen.X86.Fn.generate (Proof.RsaKeyGen.X86.Generate.srchOf v).call
        Proof.RsaKeyGen.X86.Generate.keyImpl.call
      verified := Proof.RsaKeyGen.X86.Scrub.generate_scrubbed v
      publicOutOk := Proof.RsaKeyGen.X86.Scrub.generate_public v
      spSafe := Proof.RsaKeyGen.X86.Scrub.generate_spSafe v }])

spec_apis artifacts

end VG.Artifacts.RsaKeyGen.X86
