module

public import VerifiedGarbage.Impl.Poly1305.AArch64.Vector
public import VerifiedGarbage.Proof.Poly1305.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Poly1305 (RFC 8439 §2.5) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Poly1305.AArch64

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact AArch64.target {
    code := Impl.Poly1305.AArch64.init
    verified := .scrubbed Proof.Poly1305.AArch64.Fn.init },
  Spec.Poly1305.updateApi.artifact AArch64.target {
    code := Impl.Poly1305.AArch64.Fn.update
    verified := .scrubbed Proof.Poly1305.AArch64.Fn.update },
  Spec.Poly1305.updateApi.artifact AArch64.target {
    suffix := "_neon"
    -- Faster on Apple's cores (about twice as fast), slower on Neoverse N2. It
    -- needs no feature (AdvSIMD is part of the AArch64 baseline): `neon`,
    -- which detection reports, lets `VG_CPU_FEATURES=neon` choose it
    -- elsewhere for the tests.
    extra := ["neon"]
    vendor := some "apple"
    code := Impl.Poly1305.AArch64.Fn.updateNeon
    verified := .scrubbed Proof.Poly1305.AArch64.Fn.updateNeon },
  Spec.Poly1305.finalizeApi.artifact AArch64.target {
    code := Impl.Poly1305.AArch64.Fn.finalize
    verified := .scrubbed Proof.Poly1305.AArch64.Fn.finalize }]

end VG.Artifacts.Poly1305.AArch64
