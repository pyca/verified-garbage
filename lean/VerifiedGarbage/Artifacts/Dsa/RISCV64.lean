module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParameterSearchInit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Instances
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64
public import VerifiedGarbage.Proof.Dsa.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # DSA (FIPS 186-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Dsa.RISCV64

open VG Proof.Dsa.RISCV64.PSearch
open Proof.Dsa.RISCV64.Scrub

def artifacts : List Artifact := [
  Spec.Dsa.deriveKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Dsa.RISCV64.Derive.derive
    verified := Proof.Dsa.RISCV64.deriveKey_verified } (deriveKeyOut _ [])),
  Spec.Dsa.validatePrivateKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Dsa.RISCV64.PrevalidatedSign.validate
    verified := Proof.Dsa.RISCV64.validatePrivate_verified } (validatePrivateKeyOut _ [])),
  Spec.Dsa.randomSignPrevalidatedApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Dsa.RISCV64.PrevalidatedSign.randomSign
    verified := Proof.Dsa.RISCV64.randomSignPre_verified } (randomSignPrevalidatedOut _ [])),
  Spec.Dsa.generateKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Dsa.RISCV64.Generate.code
    verified := Proof.Dsa.RISCV64.generateKey_verified } (generateKeyOut _ [])),
  Spec.Dsa.validatePublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Dsa.RISCV64.Prevalidated.validate
    verified := Proof.Dsa.RISCV64.validate_verified } (validatePublicKeyOut _ [])),
  Spec.Dsa.verifyPrevalidatedApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Dsa.RISCV64.Prevalidated.verify
    verified := Proof.Dsa.RISCV64.prevalidated_verified } (verifyPrevalidatedOut _ [])),
  Spec.Dsa.parameterInitApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Dsa.RISCV64.ParameterSearch.init
    verified := Proof.Dsa.RISCV64.init_verified } (parameterInitOut []))] ++
  (VG.Proof.Variants.MillerRabin.RISCV64.variants.attach.flatMap
    fun (v : { v : Proof.MillerRabin.RISCV64.RoundImpl // v ∈ VG.Proof.Variants.MillerRabin.RISCV64.variants }) => [
    Spec.Dsa.parameterSearchApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
      suffix := v.1.suffix
      code := Impl.Dsa.RISCV64.ParameterSearch.code (gen1 v.1) (gen2 v.1) (gen3 v.1)
      verified := params_verified v.1 } (parameterSearchOut 512 kT) 512 (Spec.Dsa.parameterSearchSig.retBits 64)
      (parameterSearchSide v.1 v.2))])

end VG.Artifacts.Dsa.RISCV64
