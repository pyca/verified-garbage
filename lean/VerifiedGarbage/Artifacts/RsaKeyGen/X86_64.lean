module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Fn
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KeyInitScrub
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SearchScrub
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64
public import VerifiedGarbage.TCB.X86_64.Print

/-! # RSA key generation (FIPS 186-5 A.1.3) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.X86_64

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact X86_64.target { code := Impl.RsaKeyGen.X86_64.Fn.keyInit, verified := .scrubbed Proof.RsaKeyGen.X86_64.KeyInit.init_scrubbed, spSafe := Proof.RsaKeyGen.X86_64.KeyInit.init_spSafe }]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.X86_64.variants.flatMap fun (v : Proof.MillerRabin.X86_64.RoundImpl) => [
    Spec.RsaKeyGen.keySearchApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.RsaKeyGen.X86_64.Fn.keySearch v.level (Proof.RsaKeyGen.X86_64.Generate.searchCall v)
      verified := .scrubbed (Proof.RsaKeyGen.X86_64.SearchScrub.keySearch_scrubbed v)
      spSafe := Proof.RsaKeyGen.X86_64.SearchScrub.keySearch_spSafe v }])

end VG.Artifacts.RsaKeyGen.X86_64
