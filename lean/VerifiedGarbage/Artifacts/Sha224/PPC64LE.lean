module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# SHA-224 (FIPS 180-4) on PPC64LE

SHA-224 is SHA-256 from another initial hash value, and its digest the first
28 bytes of the final hash value: its `init` and `finalize` are registered
here, and its `update` is SHA-256's (`Artifacts/Sha256/`). `finalize` keeps
its working space in a frame of its own, as SHA-256's does.
-/

@[expose] public section

namespace VG.Artifacts.Sha224.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact PPC64LE.target {
    code := Impl.Sha256.PPC64LE.Stream.init224
    verified := Proof.Sha256.PPC64LE.Shared.init224 },
  Spec.Sha256.finalize224Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r6 Impl.Sha256.PPC64LE.Stream.finalize224
    stack := 48 + 640
    verified := Proof.Sha256.PPC64LE.Shared.finalize224 }]

end VG.Artifacts.Sha224.PPC64LE
