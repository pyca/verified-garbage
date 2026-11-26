module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hkdf.Table
import VerifiedGarbage.Proof.Hkdf.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Impl.Hkdf.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HKDF (RFC 5869) on PPC64LE -/

namespace VG.Artifacts.Hkdf.PPC64LE

open VG.Proof.Hkdf.PPC64LE (OK)
open VG.Proof.HmacTable.PPC64LE (vars tables fnsOf)

public def artifacts : List (Artifact PPC64LE.target) :=
  if hv : OK vars then [
    Spec.Hkdf.extractApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := Impl.Hkdf.PPC64LE.Fn.extract (fnsOf vars)
      verified := Proof.Hkdf.PPC64LE.Scrub.extract_scrubbed hv },
    Spec.Hkdf.keyApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := Impl.Hkdf.PPC64LE.Fn.key (fnsOf vars)
      verified := Proof.Hkdf.PPC64LE.Scrub.key_scrubbed hv },
    Spec.Hkdf.expandApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := Impl.Hkdf.PPC64LE.Fn.expand (fnsOf vars)
      verified := Proof.Hkdf.PPC64LE.Scrub.expand_scrubbed hv }]
  else []

spec_apis artifacts

end VG.Artifacts.Hkdf.PPC64LE
