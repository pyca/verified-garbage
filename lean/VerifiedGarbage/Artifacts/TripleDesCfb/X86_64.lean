module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit
public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Verified
public import VerifiedGarbage.Proof.Variants.TripleDesEcb.X86_64

/-! # Triple DES-CFB64 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.X86_64

def direct : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncrypt
    stack := 984
    verified := Proof.TripleDes.X86_64.cfbEncrypt_framed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncryptFinal
    stack := 984
    verified := Proof.TripleDes.X86_64.cfbEncryptFinal_framed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbDecryptFinal
    stack := 984
    verified := Proof.TripleDes.X86_64.cfbDecryptFinal_framed }]

end VG.Artifacts.TripleDesCfb.X86_64

-- Triple DES-CFB64 decryption (SP 800-38A §6.3) on x86-64
namespace VG.Artifacts.TripleDesCfb.X86_64.TripleDesEcb

open VG.Proof.TripleDes.X86_64.Batch

def artifacts (v : EcbImpl) : List Artifact := [
  Spec.TripleDes.cfbDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratchWiped 2128 .r8 265
      (Impl.TripleDes.X86_64.Batch.decrypt true (v.name .encrypt) (v.code .encrypt))
    stack := 3176
    verified := cfb_framed v
    spSafe := cfb_spSafe v
    features := v.features }]

end VG.Artifacts.TripleDesCfb.X86_64.TripleDesEcb

namespace VG.Artifacts.TripleDesCfb.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.TripleDesEcb.X86_64.variants.flatMap fun v => TripleDesEcb.artifacts v)

end VG.Artifacts.TripleDesCfb.X86_64
