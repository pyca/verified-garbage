module

public import VerifiedGarbage.Proof.TripleDes.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.CbcLit

/-! # Triple DES-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.X86_64

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cbcEncryptChained
    stack := 984
    verified := Proof.TripleDes.X86_64.cbcEncryptChained_framed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cbcDecryptChained
    stack := 984
    verified := Proof.TripleDes.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.TripleDesCbc.X86_64
