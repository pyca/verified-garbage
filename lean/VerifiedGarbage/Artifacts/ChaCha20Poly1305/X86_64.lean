module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Instance
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.OpenTo
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Scrub
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.X86_64

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20Poly1305.X86_64

open VG.Proof.ChaCha20Poly1305.X86_64

def artifacts : List Artifact :=
  VG.Proof.Variants.ChaCha20Xor.X86_64.variants.flatMap fun (v : Proof.ChaCha20.X86_64.XorImpl) => [
    Spec.ChaCha20Poly1305.sealApi.artifact X86_64.target (Scrub.sealReg v),
    Spec.ChaCha20Poly1305.openZeroApi.artifact X86_64.target (Scrub.openReg v),
    Spec.ChaCha20Poly1305.openToApi.artifact X86_64.target (Scrub.openToReg v),
    Spec.ChaCha20Poly1305.sealGatherApi.artifact X86_64.target (Scrub.gatherReg v)]

end VG.Artifacts.ChaCha20Poly1305.X86_64
