module

public import VerifiedGarbage.Proof.Md5.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Md5.PPC64LE.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # MD5 (RFC 1321) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Md5.PPC64LE

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact PPC64LE.target {
    code := Impl.Md5.PPC64LE.Stream.init
    verified := Proof.Md5.PPC64LE.Shared.init
    residue := some ⟨Proof.Md5.PPC64LE.Stream.init_noResidue _ _⟩ },
  Spec.Md5.updateApi.artifact PPC64LE.target Proof.Md5.PPC64LE.updateReg,
  Spec.Md5.finalizeApi.artifact PPC64LE.target Proof.Md5.PPC64LE.finalizeReg]

end VG.Artifacts.Md5.PPC64LE
