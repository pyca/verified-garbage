module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Scrub
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # RSA key generation (FIPS 186-5 A.1.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.PPC64LE

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact PPC64LE.target {
    code := Impl.RsaKeyGen.PPC64LE.Fn.keyInit
    verified := .scrubbed Proof.RsaKeyGen.PPC64LE.Scrub.keyInit_scrubbed }]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.attach.map fun ⟨v, hv⟩ =>
    Spec.RsaKeyGen.keySearchApi.artifact PPC64LE.target {
      suffix := v.suffix
      code := Impl.RsaKeyGen.PPC64LE.Fn.keySearch v.suffix v.code
      verified := .scrubbed (Proof.RsaKeyGen.PPC64LE.Scrub.keySearch_scrubbed v hv) })

end VG.Artifacts.RsaKeyGen.PPC64LE
