module

public import VerifiedGarbage.Proof.Cast5.X86_64.CbcVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.X86_64

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact X86_64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 Impl.Cast5.X86_64.cbcEncryptChained
    stack := 240
    verified := Proof.Cast5.X86_64.cbcEncryptChained_framed },
  Spec.Cast5.cbcDecryptChainedApi.artifact X86_64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 Impl.Cast5.X86_64.cbcDecryptChained
    stack := 240
    verified := Proof.Cast5.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.Cast5Cbc.X86_64
