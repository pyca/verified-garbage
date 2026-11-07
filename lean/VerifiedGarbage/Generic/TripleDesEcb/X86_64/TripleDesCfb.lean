module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Triple DES-CFB64 decryption (SP 800-38A §6.3) on x86-64 -/

@[expose] public section

namespace VG.Generic.TripleDesEcb.X86_64.TripleDesCfb

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

end VG.Generic.TripleDesEcb.X86_64.TripleDesCfb
