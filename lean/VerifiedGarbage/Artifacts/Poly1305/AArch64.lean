module

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
    verified := .scrubbed ⟨Proof.Poly1305.AArch64.init_verified, Proof.Poly1305.AArch64.init_noResidue _⟩ },
  Spec.Poly1305.updateApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Radix64.update
    verified := Proof.Poly1305.AArch64.Radix64.update_framed }
    (Proof.Poly1305.AArch64.Scrub.updateOk 128)),
  Spec.Poly1305.updateApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
    suffix := "_neon"
    -- Faster on Apple's cores (about twice as fast), slower on Neoverse N2. It
    -- needs no feature (AdvSIMD is part of the AArch64 baseline): `neon`,
    -- which detection reports, lets `VG_CPU_FEATURES=neon` choose it
    -- elsewhere for the tests.
    extra := ["neon"]
    vendor := some "apple"
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Vector.update
    verified := Proof.Poly1305.AArch64.Vector.update_framed }
    (Proof.Poly1305.AArch64.Scrub.updateOk 128)),
  Spec.Poly1305.finalizeApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x3 Impl.Poly1305.AArch64.Radix64.finalize
    verified := Proof.Poly1305.AArch64.Radix64.finalize_framed }
    (Proof.Poly1305.AArch64.Scrub.finalizeOk 128))]

end VG.Artifacts.Poly1305.AArch64
