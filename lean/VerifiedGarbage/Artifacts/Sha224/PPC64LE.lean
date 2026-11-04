module

import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Digest

/-! # SHA-224 (FIPS 180-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha224.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact PPC64LE.target {
    code := Impl.Sha256.PPC64LE.Stream.init224
    verified := Proof.Sha256.PPC64LE.Shared.init224 },
  Spec.Sha256.finalize224Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r6 Impl.Sha256.PPC64LE.Stream.finalize224
    stack := 48 + 640
    verified := Proof.Sha256.PPC64LE.Shared.finalize224 },
  Spec.Sha256.digest224Api.artifact PPC64LE.target {
    code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha224.hash
    stack := 96 + Impl.MdStream.PPC64LE.Digest.frameBytes Proof.Hmac.Stream.PPC64LE.Sha224.hash
    verified := Proof.Sha256.PPC64LE.Digest.Sha224.verified }]

end VG.Artifacts.Sha224.PPC64LE
