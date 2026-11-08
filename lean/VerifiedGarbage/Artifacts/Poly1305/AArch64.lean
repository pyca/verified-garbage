module

public import VerifiedGarbage.Proof.Poly1305.AArch64.Init
public import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Update
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Frame
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
    verified := Proof.Poly1305.AArch64.init_verified },
  Spec.Poly1305.updateApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Radix64.update
    stack := 128
    verified := Proof.Poly1305.AArch64.Radix64.update_framed },
  Spec.Poly1305.updateApi.artifact AArch64.target {
    suffix := "_neon"
    -- Faster on Apple's cores (about twice as fast), slower on Neoverse N2. It
    -- needs no feature (AdvSIMD is part of the AArch64 baseline): `neon`,
    -- which detection reports, lets `VG_CPU_FEATURES=neon` choose it
    -- elsewhere for the tests.
    extra := ["neon"]
    vendor := some "apple"
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Vector.update
    stack := 128
    verified := Proof.Poly1305.AArch64.Vector.update_framed },
  Spec.Poly1305.finalizeApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x3 Impl.Poly1305.AArch64.Radix64.finalize
    stack := 128
    verified := Proof.Poly1305.AArch64.Radix64.finalize_framed }]

end VG.Artifacts.Poly1305.AArch64
