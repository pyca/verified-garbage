module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hkdf.Table
import VerifiedGarbage.Proof.Hkdf.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Impl.Hkdf.AArch64.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HKDF (RFC 5869) on AArch64 -/

namespace VG.Artifacts.Hkdf.AArch64

open VG.Proof.HmacTable.AArch64 (tables fnsOf)
open VG.Proof.Variants.MdHash.AArch64 (variants)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Hkdf.keyApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Hkdf.AArch64.Fn.key (fnsOf variants)
    verified := Proof.Hkdf.AArch64.Scrub.key_scrubbedV },
  Spec.Hkdf.extractApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Hkdf.AArch64.Fn.extract (fnsOf variants)
    verified := Proof.Hkdf.AArch64.Scrub.extract_scrubbedV },
  Spec.Hkdf.expandApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Hkdf.AArch64.Fn.expand (fnsOf variants)
    verified := Proof.Hkdf.AArch64.Scrub.expand_scrubbedV }]

spec_apis artifacts

end VG.Artifacts.Hkdf.AArch64
