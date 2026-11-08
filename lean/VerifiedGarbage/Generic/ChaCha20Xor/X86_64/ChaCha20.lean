module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.ApplyCT
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Streaming ChaCha20 (RFC 8439) on x86-64: `vg_chacha20_apply` -/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.X86_64.ChaCha20

def artifacts (v : Proof.ChaCha20.X86_64.XorImpl) : List Artifact :=
  if v.polyOnly then [] else [
  Spec.ChaCha20.applyApi.artifact X86_64.target (Proof.ChaCha20.X86_64.Scrub.applyReg v)]

end VG.Generic.ChaCha20Xor.X86_64.ChaCha20
