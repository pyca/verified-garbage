module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hkdf.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
public import VerifiedGarbage.Impl.Hkdf.PPC64LE.Fn
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # HKDF (RFC 5869) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Hkdf.PPC64LE

open VG.Proof.Hkdf.PPC64LE (OK)
open VG.Proof.HmacTable.PPC64LE (vars tables fnsOf)

def artifacts : List Artifact :=
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

end VG.Artifacts.Hkdf.PPC64LE
