module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit

/-! # Triple DES-CFB8 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.X86_64

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.cfb8EncryptReg,
  Spec.TripleDes.cfb8DecryptApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.cfb8DecryptReg]

end VG.Artifacts.TripleDesCfb8.X86_64
