module

public import VerifiedGarbage.Proof.TripleDes.X86_64.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.TripleDes.X86_64.CbcLit
public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Verified
public import VerifiedGarbage.Proof.Variants.TripleDesEcb.X86_64

/-! # Triple DES-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.X86_64

def direct : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.cbcEncryptReg]

end VG.Artifacts.TripleDesCbc.X86_64

namespace VG.Artifacts.TripleDesCbc.X86_64

open VG.Proof.TripleDes.X86_64.Batch

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.TripleDesEcb.X86_64.variants.flatMap fun (v : EcbImpl) => [
    Spec.TripleDes.cbcDecryptChainedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratchWiped 2128 .r8 265
        (Impl.TripleDes.X86_64.Batch.decrypt false (v.name .decrypt) (v.code .decrypt))
      stack := 3176
      verified := cbc_framed v
      spSafe := cbc_spSafe v }])

end VG.Artifacts.TripleDesCbc.X86_64
