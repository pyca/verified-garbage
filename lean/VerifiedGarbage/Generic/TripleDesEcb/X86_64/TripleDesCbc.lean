module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Triple DES-CBC decryption (SP 800-38A §6.2) on x86-64 -/

@[expose] public section

namespace VG.Generic.TripleDesEcb.X86_64.TripleDesCbc

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

end VG.Generic.TripleDesEcb.X86_64.TripleDesCbc
