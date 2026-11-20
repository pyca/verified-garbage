module

public import VerifiedGarbage.Proof.Sm3.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Sm3.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Sm3.PPC64LE.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # SM3 (GB/T 32905-2016) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm3.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact PPC64LE.target {
    code := Impl.Sm3.PPC64LE.Stream.init
    verified := .scrubbed ⟨Proof.Sm3.PPC64LE.Shared.init, Proof.Sm3.PPC64LE.Stream.init_noResidue _ _⟩ },
  Spec.Sm3.updateApi.artifact PPC64LE.target Proof.Sm3.PPC64LE.updateReg,
  Spec.Sm3.finalizeApi.artifact PPC64LE.target Proof.Sm3.PPC64LE.finalizeReg]

end VG.Artifacts.Sm3.PPC64LE
