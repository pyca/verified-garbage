module

public import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # SHA-1 (FIPS 180-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha1.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Stream.init
    verified := Proof.Sha1.PPC64LE.Shared.init
    residue := some ⟨Proof.Sha1.PPC64LE.Stream.init_noResidue _ _⟩ },
  Spec.Sha1.updateApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sha1.PPC64LE.Stream.update
    verified := Proof.Sha1.PPC64LE.Shared.update },
  Spec.Sha1.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sha1.PPC64LE.Stream.finalize
    verified := Proof.Sha1.PPC64LE.Shared.finalize },
  Spec.Sha1.digestApi.artifact PPC64LE.target {
    code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha1.hash
    verified := Proof.Hmac.Stream.PPC64LE.Sha1.digest }]

end VG.Artifacts.Sha1.PPC64LE
