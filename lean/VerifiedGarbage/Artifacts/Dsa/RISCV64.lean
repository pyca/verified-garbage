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

/-! # DSA (FIPS 186-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Dsa.RISCV64

open VG Proof.Dsa.RISCV64.PSearch

def artifacts : List Artifact := [
  Spec.Dsa.deriveKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Derive.derive
    verified := Proof.Dsa.RISCV64.deriveKey_verified },
  Spec.Dsa.validatePrivateKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.PrevalidatedSign.validate
    verified := Proof.Dsa.RISCV64.validatePrivate_verified },
  Spec.Dsa.randomSignPrevalidatedApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.PrevalidatedSign.randomSign
    verified := Proof.Dsa.RISCV64.randomSignPre_verified },
  Spec.Dsa.generateKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Generate.code
    verified := Proof.Dsa.RISCV64.generateKey_verified },
  Spec.Dsa.validatePublicKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Prevalidated.validate
    verified := Proof.Dsa.RISCV64.validate_verified },
  Spec.Dsa.verifyPrevalidatedApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Prevalidated.verify
    verified := Proof.Dsa.RISCV64.prevalidated_verified },
  Spec.Dsa.parameterInitApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.ParameterSearch.init
    verified := Proof.Dsa.RISCV64.init_verified }] ++
  (VG.Proof.Variants.MillerRabin.RISCV64.variants.flatMap fun (v : Proof.MillerRabin.RISCV64.RoundImpl) => [
    Spec.Dsa.parameterSearchApi.artifact RISCV64.target {
      suffix := v.suffix
      code := Impl.Dsa.RISCV64.ParameterSearch.code (gen1 v) (gen2 v) (gen3 v)
      verified := params_verified v }])

end VG.Artifacts.Dsa.RISCV64
