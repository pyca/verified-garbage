module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hkdf.Table
import VerifiedGarbage.Proof.Hkdf.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Impl.Hkdf.X86.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HKDF (RFC 5869) on x86 -/

namespace VG.Artifacts.Hkdf.X86

open VG.Proof.HmacTable.X86 (tables fnsOf)
open VG.Proof.Hkdf.X86 (OK)
open VG.Proof.Hkdf.X86.Scrub (vs)

public def artifacts : List (Artifact X86.target) :=
  if hO : OK vs then [
    Spec.Hkdf.keyApi.artifact X86.target {
      tables := [("hmac", tables vs)]
      code := Impl.Hkdf.X86.Fn.key (fnsOf vs)
      verified := Proof.Hkdf.X86.Scrub.key_scrubbedV hO
      spSafe := Proof.Hkdf.X86.Scrub.key_spSafe vs },
    Spec.Hkdf.extractApi.artifact X86.target {
      tables := [("hmac", tables vs)]
      code := Impl.Hkdf.X86.Fn.extract (fnsOf vs)
      verified := Proof.Hkdf.X86.Scrub.extract_scrubbedV hO
      spSafe := Proof.Hkdf.X86.Scrub.extract_spSafe vs },
    Spec.Hkdf.expandApi.artifact X86.target {
      tables := [("hmac", tables vs)]
      code := Impl.Hkdf.X86.Fn.expand (fnsOf vs)
      verified := Proof.Hkdf.X86.Scrub.expand_scrubbedV hO
      spSafe := Proof.Hkdf.X86.Scrub.expand_spSafe vs }]
  else []

spec_apis artifacts

end VG.Artifacts.Hkdf.X86
