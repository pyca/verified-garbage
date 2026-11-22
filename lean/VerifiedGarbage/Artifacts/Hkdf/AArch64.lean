module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Hkdf.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Impl.Hkdf.AArch64.Fn
public import VerifiedGarbage.TCB.AArch64.Print

/-! # HKDF (RFC 5869) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Hkdf.AArch64

open VG.Proof.HmacTable.AArch64 (tables fnsOf)
open VG.Proof.Variants.MdHash.AArch64 (variants)

def artifacts : List Artifact := [
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

end VG.Artifacts.Hkdf.AArch64
