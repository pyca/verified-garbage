module

public import VerifiedGarbage.Proof.TripleDes.X86.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.CbcLit

/-! # Triple DES-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.X86

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cbcEncryptChained
    stack := 984
    verified := Proof.TripleDes.X86.Cbc.cbcEncryptChained_framed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cbcDecryptChained
    stack := 984
    verified := Proof.TripleDes.X86.Cbc.cbcDecryptChained_framed }]

end VG.Artifacts.TripleDesCbc.X86
