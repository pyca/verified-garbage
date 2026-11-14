module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Shared
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224

/-! # SHA-256 (FIPS 180-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha256.PPC64LE

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
    verified := Proof.Hmac.Stream.PPC64LE.Sha224.digest },
  Spec.Sha256.initApi.artifact PPC64LE.target {
    code := Impl.Sha256.PPC64LE.Stream.init
    verified := Proof.Sha256.PPC64LE.Shared.init },
  Spec.Sha256.updateApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r7 Impl.Sha256.PPC64LE.Stream.update
    stack := 688
    verified := Proof.Sha256.PPC64LE.Shared.update },
  Spec.Sha256.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r6 Impl.Sha256.PPC64LE.Stream.finalize
    stack := 688
    verified := Proof.Sha256.PPC64LE.Shared.finalize },
  Spec.Sha256.digest256Api.artifact PPC64LE.target {
    code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha256.hash
    stack := 96 + Impl.MdStream.PPC64LE.Digest.frameBytes Proof.Hmac.Stream.PPC64LE.Sha256.hash
    verified := Proof.Hmac.Stream.PPC64LE.Sha256.digest }]

end VG.Artifacts.Sha256.PPC64LE
