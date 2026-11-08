module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86

/-! # RSA key generation (FIPS 186-5 A.1.3) on baseline i686 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.X86

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact X86.target {
    code := Impl.RsaKeyGen.X86.KeyInit.init
    verified := Proof.RsaKeyGen.X86.KeyInit.init_verified }]

end VG.Artifacts.RsaKeyGen.X86

-- RSA key generation on i686, its prime searches' candidates calling each shared Miller–Rabin implementation
namespace VG.Artifacts.RsaKeyGen.X86.MillerRabin
open VG VG.X86 VG.Proof.MillerRabin.X86

def artifacts (v : RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.keySearchApi.artifact target {
    suffix := v.suffix
    code := Proof.RsaKeyGen.X86.Generate.genCode v
    stack := 284
    verified := Proof.RsaKeyGen.X86.Generate.gen_verified v
    spSafe := Proof.RsaKeyGen.X86.Generate.genCode_sp v
    features := v.features }]

end VG.Artifacts.RsaKeyGen.X86.MillerRabin

namespace VG.Artifacts.RsaKeyGen.X86

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.X86.variants.flatMap fun v => MillerRabin.artifacts v)

end VG.Artifacts.RsaKeyGen.X86
