module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Poly1305.AArch64.Init
public import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Update
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Frame
public import VerifiedGarbage.Proof.Poly1305.AArch64.Scrub
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Poly1305 (RFC 8439 §2.5) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Poly1305.AArch64

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact AArch64.target {
    code := Impl.Poly1305.AArch64.init
    verified := Proof.Poly1305.AArch64.init_verified
    residue := some ⟨Proof.Poly1305.AArch64.init_noResidue _⟩ },
  Spec.Poly1305.updateApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Radix64.update
    verified := Proof.Poly1305.AArch64.Radix64.update_framed }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [],
       []⟩
    (Proof.Poly1305.AArch64.Scrub.updateOk 128)),
  Spec.Poly1305.updateApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := "_neon"
    -- Faster on Apple's cores (about twice as fast), slower on Neoverse N2. It
    -- needs no feature (AdvSIMD is part of the AArch64 baseline): `neon`,
    -- which detection reports, lets `VG_CPU_FEATURES=neon` choose it
    -- elsewhere for the tests.
    extra := ["neon"]
    vendor := some "apple"
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Vector.update
    verified := Proof.Poly1305.AArch64.Vector.update_framed }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
       .v26, .v27, .v28, .v29, .v30, .v31],
       [.v8, .v9, .v10, .v11, .v12, .v13, .v14]⟩
    (Proof.Poly1305.AArch64.Scrub.updateOk 128)),
  Spec.Poly1305.finalizeApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x3 Impl.Poly1305.AArch64.Radix64.finalize
    verified := Proof.Poly1305.AArch64.Radix64.finalize_framed }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [],
       []⟩
    (Proof.Poly1305.AArch64.Scrub.finalizeOk 128))]

end VG.Artifacts.Poly1305.AArch64
