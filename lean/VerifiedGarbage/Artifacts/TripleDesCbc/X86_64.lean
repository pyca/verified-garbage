module

public import VerifiedGarbage.Proof.TripleDes.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.TripleDes.X86_64.CbcLit
public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Verified
public import VerifiedGarbage.Proof.Variants.TripleDesEcb.X86_64

/-! # Triple DES-CBC encryption on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.X86_64

def direct : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cbcEncryptChained
    stack := 984
    verified := Proof.TripleDes.X86_64.cbcEncryptChained_framed }]

end VG.Artifacts.TripleDesCbc.X86_64

-- Triple DES-CBC decryption (SP 800-38A §6.2) on x86-64
namespace VG.Artifacts.TripleDesCbc.X86_64.TripleDesEcb

open VG.Proof.TripleDes.X86_64.Batch

def artifacts (v : EcbImpl) : List Artifact := [
  Spec.TripleDes.cbcDecryptChainedApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratchWiped 2128 .r8 265
      (Impl.TripleDes.X86_64.Batch.decrypt false (v.name .decrypt) (v.code .decrypt))
    stack := 3176
    verified := cbc_framed v
    spSafe := cbc_spSafe v
    features := v.features }]

end VG.Artifacts.TripleDesCbc.X86_64.TripleDesEcb

namespace VG.Artifacts.TripleDesCbc.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.TripleDesEcb.X86_64.variants.flatMap fun v => TripleDesEcb.artifacts v)

end VG.Artifacts.TripleDesCbc.X86_64
