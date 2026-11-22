module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Hkdf.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64
public import VerifiedGarbage.Impl.Hkdf.X86_64.Fn
public import VerifiedGarbage.TCB.X86_64.Print

/-! # HKDF (RFC 5869) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Hkdf.X86_64

open VG.Proof.HmacTable.X86_64 (tables fnsOf)
open VG.Proof.Variants.MdHash.X86_64 (variants)
open VG.Proof.Hkdf.X86_64 (OK)

def artifacts : List Artifact :=
  if hO : OK variants then [
    Spec.Hkdf.keyApi.artifact X86_64.target {
      tables := [("hmac", tables variants)]
      code := Impl.Hkdf.X86_64.Fn.key (fnsOf variants)
      verified := Proof.Hkdf.X86_64.Scrub.key_scrubbedV hO
      spSafe := Proof.Hkdf.X86_64.Scrub.key_spSafe variants },
    Spec.Hkdf.extractApi.artifact X86_64.target {
      tables := [("hmac", tables variants)]
      code := Impl.Hkdf.X86_64.Fn.extract (fnsOf variants)
      verified := Proof.Hkdf.X86_64.Scrub.extract_scrubbedV hO
      spSafe := Proof.Hkdf.X86_64.Scrub.extract_spSafe variants },
    Spec.Hkdf.expandApi.artifact X86_64.target {
      tables := [("hmac", tables variants)]
      code := Impl.Hkdf.X86_64.Fn.expand (fnsOf variants)
      verified := Proof.Hkdf.X86_64.Scrub.expand_scrubbedV hO
      spSafe := Proof.Hkdf.X86_64.Scrub.expand_spSafe variants }]
  else []

end VG.Artifacts.Hkdf.X86_64
