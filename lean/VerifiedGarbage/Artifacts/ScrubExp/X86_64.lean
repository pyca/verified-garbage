module

public import VerifiedGarbage.Proof.Poly1305.X86_64.ScrubExp

/-! # Experiment: Poly1305 without secret residue (x86-64), for measuring -/

@[expose] public section

namespace VG.Artifacts.ScrubExp.X86_64

open VG.Proof.Poly1305.X86_64.ScrubExp

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact X86_64.target init,
  Spec.Poly1305.updateApi.artifact X86_64.target update,
  Spec.Poly1305.finalizeApi.artifact X86_64.target finalize]

end VG.Artifacts.ScrubExp.X86_64
