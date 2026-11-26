module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Impl.Poly1305.AArch64.Vector
import VerifiedGarbage.Proof.Poly1305.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Poly1305 (RFC 8439 §2.5) on AArch64 -/

namespace VG.Artifacts.Poly1305.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Poly1305.initApi.artifact AArch64.target {
    code := Impl.Poly1305.AArch64.init
    verified := Proof.Poly1305.AArch64.Fn.init },
  Spec.Poly1305.updateApi.artifact AArch64.target {
    code := Impl.Poly1305.AArch64.Fn.update
    verified := Proof.Poly1305.AArch64.Fn.update },
  Spec.Poly1305.updateApi.artifact AArch64.target {
    suffix := "_neon"
    -- Faster on Apple's cores (about twice as fast), slower on Neoverse N2. It
    -- needs no feature (AdvSIMD is part of the AArch64 baseline): `neon`,
    -- which detection reports, lets `VG_CPU_FEATURES=neon` choose it
    -- elsewhere for the tests.
    extra := ["neon"]
    vendor := some "apple"
    code := Impl.Poly1305.AArch64.Fn.updateNeon
    verified := Proof.Poly1305.AArch64.Fn.updateNeon },
  Spec.Poly1305.finalizeApi.artifact AArch64.target {
    code := Impl.Poly1305.AArch64.Fn.finalize
    verified := Proof.Poly1305.AArch64.Fn.finalize }]

spec_apis artifacts

end VG.Artifacts.Poly1305.AArch64
