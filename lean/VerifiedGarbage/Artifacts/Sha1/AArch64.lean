module

public import VerifiedGarbage.Proof.Sha1.AArch64.Shared
public import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Compress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-1 (FIPS 180-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha1.AArch64

def artifacts : List Artifact := [
  Spec.Sha1.compressApi.artifact AArch64.target {
    code := Impl.Sha1.AArch64.compress
    verified := Proof.Sha1.AArch64.Shared.compress },
  Spec.Sha1.initApi.artifact AArch64.target {
    code := Impl.Sha1.AArch64.Stream.init
    verified := Proof.Sha1.AArch64.Shared.init },
  Spec.Sha1.compressApi.artifact AArch64.target {
    suffix := "_sha2"
    notes := ["Uses the AArch64 SHA-1 instructions. \
      The four round constants are built in AdvSIMD registers once, before the first block, \
      and the state stays in registers between blocks."]
    code := Impl.Sha1.AArch64.Sha2.compress
    verified := Proof.Sha1.AArch64.Shared.compress_of Proof.Sha1.AArch64.Sha2.compress_verified
    features := ["sha2"] }]

end VG.Artifacts.Sha1.AArch64
