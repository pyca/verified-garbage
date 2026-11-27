module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
import VerifiedGarbage.Proof.MlDsa.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ML-DSA (FIPS 204) on RISC-V -/

namespace VG.Artifacts.MlDsa.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.MlDsa.keyGen44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.keyGen44
    verified := Proof.MlDsa.RISCV64.Scrub.keyGen44_scrubbed },
  Spec.MlDsa.keyGen65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.keyGen65
    verified := Proof.MlDsa.RISCV64.Scrub.keyGen65_scrubbed },
  Spec.MlDsa.keyGen87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.keyGen87
    verified := Proof.MlDsa.RISCV64.Scrub.keyGen87_scrubbed },
  Spec.MlDsa.pkTr44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.pkTr44
    verified := Proof.MlDsa.RISCV64.Scrub.pkTr44_scrubbed },
  Spec.MlDsa.pkTr65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.pkTr65
    verified := Proof.MlDsa.RISCV64.Scrub.pkTr65_scrubbed },
  Spec.MlDsa.pkTr87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.pkTr87
    verified := Proof.MlDsa.RISCV64.Scrub.pkTr87_scrubbed },
  Spec.MlDsa.preparePublicKey44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.preparePublic44
    verified := Proof.MlDsa.RISCV64.Scrub.preparePublic44_scrubbed },
  Spec.MlDsa.prepareSecretKey44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.prepareSecret44
    verified := Proof.MlDsa.RISCV64.Scrub.prepareSecret44_scrubbed },
  Spec.MlDsa.preparePublicKey65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.preparePublic65
    verified := Proof.MlDsa.RISCV64.Scrub.preparePublic65_scrubbed },
  Spec.MlDsa.prepareSecretKey65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.prepareSecret65
    verified := Proof.MlDsa.RISCV64.Scrub.prepareSecret65_scrubbed },
  Spec.MlDsa.preparePublicKey87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.preparePublic87
    verified := Proof.MlDsa.RISCV64.Scrub.preparePublic87_scrubbed },
  Spec.MlDsa.prepareSecretKey87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.prepareSecret87
    verified := Proof.MlDsa.RISCV64.Scrub.prepareSecret87_scrubbed },
  Spec.MlDsa.sign44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.sign44
    verified := Proof.MlDsa.RISCV64.Scrub.sign44_scrubbed },
  Spec.MlDsa.sign65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.sign65
    verified := Proof.MlDsa.RISCV64.Scrub.sign65_scrubbed },
  Spec.MlDsa.sign87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.sign87
    verified := Proof.MlDsa.RISCV64.Scrub.sign87_scrubbed },
  Spec.MlDsa.preparedSign44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.signPrepared44
    verified := Proof.MlDsa.RISCV64.Scrub.signPrepared44_scrubbed },
  Spec.MlDsa.preparedSign65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.signPrepared65
    verified := Proof.MlDsa.RISCV64.Scrub.signPrepared65_scrubbed },
  Spec.MlDsa.preparedSign87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.signPrepared87
    verified := Proof.MlDsa.RISCV64.Scrub.signPrepared87_scrubbed },
  Spec.MlDsa.signMessage44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.signMessage44
    verified := Proof.MlDsa.RISCV64.Scrub.signMessage44_scrubbed },
  Spec.MlDsa.signMessage65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.signMessage65
    verified := Proof.MlDsa.RISCV64.Scrub.signMessage65_scrubbed },
  Spec.MlDsa.signMessage87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.signMessage87
    verified := Proof.MlDsa.RISCV64.Scrub.signMessage87_scrubbed },
  Spec.MlDsa.preparedSignMessage44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.preparedSignMessage44
    verified := Proof.MlDsa.RISCV64.Scrub.preparedSignMessage44_scrubbed },
  Spec.MlDsa.preparedSignMessage65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.preparedSignMessage65
    verified := Proof.MlDsa.RISCV64.Scrub.preparedSignMessage65_scrubbed },
  Spec.MlDsa.preparedSignMessage87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.preparedSignMessage87
    verified := Proof.MlDsa.RISCV64.Scrub.preparedSignMessage87_scrubbed },
  Spec.MlDsa.verify44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.verify44
    verified := Proof.MlDsa.RISCV64.Scrub.verify44_scrubbed },
  Spec.MlDsa.verify65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.verify65
    verified := Proof.MlDsa.RISCV64.Scrub.verify65_scrubbed },
  Spec.MlDsa.verify87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.verify87
    verified := Proof.MlDsa.RISCV64.Scrub.verify87_scrubbed },
  Spec.MlDsa.preparedVerify44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.verifyPrepared44
    verified := Proof.MlDsa.RISCV64.Scrub.verifyPrepared44_scrubbed },
  Spec.MlDsa.preparedVerify65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.verifyPrepared65
    verified := Proof.MlDsa.RISCV64.Scrub.verifyPrepared65_scrubbed },
  Spec.MlDsa.preparedVerify87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.verifyPrepared87
    verified := Proof.MlDsa.RISCV64.Scrub.verifyPrepared87_scrubbed },
  Spec.MlDsa.verifyMessageCached44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.verifyMessageCached44
    verified := Proof.MlDsa.RISCV64.Scrub.verifyMessageCached44_scrubbed },
  Spec.MlDsa.verifyMessageCached65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.verifyMessageCached65
    verified := Proof.MlDsa.RISCV64.Scrub.verifyMessageCached65_scrubbed },
  Spec.MlDsa.verifyMessageCached87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.verifyMessageCached87
    verified := Proof.MlDsa.RISCV64.Scrub.verifyMessageCached87_scrubbed },
  Spec.MlDsa.preparedVerifyMessage44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.preparedVerifyMessage44
    verified := Proof.MlDsa.RISCV64.Scrub.preparedVerifyMessage44_scrubbed },
  Spec.MlDsa.preparedVerifyMessage65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.preparedVerifyMessage65
    verified := Proof.MlDsa.RISCV64.Scrub.preparedVerifyMessage65_scrubbed },
  Spec.MlDsa.preparedVerifyMessage87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Fn.preparedVerifyMessage87
    verified := Proof.MlDsa.RISCV64.Scrub.preparedVerifyMessage87_scrubbed }]

spec_apis artifacts

end VG.Artifacts.MlDsa.RISCV64
