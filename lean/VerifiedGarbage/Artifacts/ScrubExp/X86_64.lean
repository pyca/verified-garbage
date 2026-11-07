module

public import VerifiedGarbage.Proof.Poly1305.X86_64.ScrubExp
public import VerifiedGarbage.Proof.ChaCha20.X86_64.ScrubExp

/-! # Experiment: Poly1305 without secret residue (x86-64), for measuring -/

@[expose] public section

namespace VG.Artifacts.ScrubExp.X86_64

open VG.Proof.Poly1305.X86_64.ScrubExp

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact X86_64.target init,
  Spec.Poly1305.updateApi.artifact X86_64.target update,
  Spec.Poly1305.finalizeApi.artifact X86_64.target finalize,
  Spec.ChaCha20.applyApi.artifact X86_64.target Proof.ChaCha20.X86_64.ScrubExp.applyScalar,
  Spec.ChaCha20.applyApi.artifact X86_64.target Proof.ChaCha20.X86_64.ScrubExp.applyAvx2,
  Spec.ChaCha20.applyApi.artifact X86_64.target Proof.ChaCha20.X86_64.ScrubExp.applyAvx512]

end VG.Artifacts.ScrubExp.X86_64
