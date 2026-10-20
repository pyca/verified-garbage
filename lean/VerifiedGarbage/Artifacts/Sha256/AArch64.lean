module

public import VerifiedGarbage.Proof.Sha256.AArch64.Shared
public import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Compress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-256 (FIPS 180-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha256.AArch64

def artifacts : List Artifact := [
  Spec.Sha256.compressApi.artifact AArch64.target {
    code := Impl.Sha256.AArch64.compress
    verified := Proof.Sha256.AArch64.Shared.compress },
  Spec.Sha256.initApi.artifact AArch64.target {
    code := Impl.Sha256.AArch64.Stream.init
    verified := Proof.Sha256.AArch64.Shared.init },
  Spec.Sha256.compressApi.artifact AArch64.target {
    suffix := "_sha2"
    notes := ["Uses the AArch64 SHA-256 instructions. \
      The state stays in AdvSIMD registers between blocks, each block copying its original \
      state to `v30` and `v31` for the feed-forward, and is stored once, after the last block. \
      The first block builds the round-constant vectors of the first fourteen groups of rounds, \
      each just before its rounds, in `v16`–`v29`, where the later blocks find them; the last \
      two groups load theirs every block."]
    code := Impl.Sha256.AArch64.Sha2.compress
    verified := Proof.Sha256.AArch64.Shared.compress_of Proof.Sha256.AArch64.Sha2.compress_verified
    features := ["sha2"] }]

end VG.Artifacts.Sha256.AArch64
