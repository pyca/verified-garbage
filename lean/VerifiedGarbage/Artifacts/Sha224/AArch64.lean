module

public import VerifiedGarbage.Proof.Sha256.AArch64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# SHA-224 (FIPS 180-4) on AArch64

SHA-224 is SHA-256 from another initial hash value, and its digest the first
28 bytes of the final hash value: its `init` is registered here, its
`update` is SHA-256's (`Artifacts/Sha256/`), and its `finalize`, which
writes its digest, is emitted with each compression function
(`Proof/Pbkdf2/Md/AArch64/Hashes/Sha224.lean`).
-/

@[expose] public section

namespace VG.Artifacts.Sha224.AArch64

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact AArch64.target {
    code := Impl.Sha256.AArch64.Stream.init224
    verified := Proof.Sha256.AArch64.Shared.init224 }]

end VG.Artifacts.Sha224.AArch64
