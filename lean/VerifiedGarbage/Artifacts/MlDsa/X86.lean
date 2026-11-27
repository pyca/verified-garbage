module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
import VerifiedGarbage.Proof.MlDsa.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ML-DSA (FIPS 204) on x86 -/

namespace VG.Artifacts.MlDsa.X86

open VG

public def artifacts : List (Artifact X86.target) := [
  Spec.MlDsa.keyGen44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.keyGen Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.X86.Scrub.keyGen_scrubbed "mldsa44" "ML-DSA-44" Proof.MlDsa.X86.Scrub.inst44.params
    spSafe := Proof.MlDsa.X86.Scrub.keyGen_spSafe _ },
  Spec.MlDsa.keyGen65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.keyGen Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.X86.Scrub.keyGen_scrubbed "mldsa65" "ML-DSA-65" Proof.MlDsa.X86.Scrub.inst65.params
    spSafe := Proof.MlDsa.X86.Scrub.keyGen_spSafe _ },
  Spec.MlDsa.keyGen87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.keyGen Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.X86.Scrub.keyGen_scrubbed "mldsa87" "ML-DSA-87" Proof.MlDsa.X86.Scrub.inst87.params
    spSafe := Proof.MlDsa.X86.Scrub.keyGen_spSafe _ },
  Spec.MlDsa.pkTr44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.pkTr Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.X86.Scrub.pkTr_scrubbed "mldsa44" "ML-DSA-44" Proof.MlDsa.X86.Scrub.inst44.params
    spSafe := Proof.MlDsa.X86.Scrub.pkTr_spSafe _ },
  Spec.MlDsa.pkTr65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.pkTr Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.X86.Scrub.pkTr_scrubbed "mldsa65" "ML-DSA-65" Proof.MlDsa.X86.Scrub.inst65.params
    spSafe := Proof.MlDsa.X86.Scrub.pkTr_spSafe _ },
  Spec.MlDsa.pkTr87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.pkTr Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.X86.Scrub.pkTr_scrubbed "mldsa87" "ML-DSA-87" Proof.MlDsa.X86.Scrub.inst87.params
    spSafe := Proof.MlDsa.X86.Scrub.pkTr_spSafe _ },
  Spec.MlDsa.preparePublicKey44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparePublic Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.X86.Scrub.preparePublic_scrubbed "mldsa44" "ML-DSA-44" Proof.MlDsa.X86.Scrub.inst44.params
    spSafe := Proof.MlDsa.X86.Scrub.preparePublic_spSafe _ },
  Spec.MlDsa.prepareSecretKey44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.prepareSecret Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.X86.Scrub.prepareSecret_scrubbed "mldsa44" "ML-DSA-44" Proof.MlDsa.X86.Scrub.inst44.params
    spSafe := Proof.MlDsa.X86.Scrub.prepareSecret_spSafe _ },
  Spec.MlDsa.preparePublicKey65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparePublic Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.X86.Scrub.preparePublic_scrubbed "mldsa65" "ML-DSA-65" Proof.MlDsa.X86.Scrub.inst65.params
    spSafe := Proof.MlDsa.X86.Scrub.preparePublic_spSafe _ },
  Spec.MlDsa.prepareSecretKey65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.prepareSecret Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.X86.Scrub.prepareSecret_scrubbed "mldsa65" "ML-DSA-65" Proof.MlDsa.X86.Scrub.inst65.params
    spSafe := Proof.MlDsa.X86.Scrub.prepareSecret_spSafe _ },
  Spec.MlDsa.preparePublicKey87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparePublic Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.X86.Scrub.preparePublic_scrubbed "mldsa87" "ML-DSA-87" Proof.MlDsa.X86.Scrub.inst87.params
    spSafe := Proof.MlDsa.X86.Scrub.preparePublic_spSafe _ },
  Spec.MlDsa.prepareSecretKey87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.prepareSecret Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.X86.Scrub.prepareSecret_scrubbed "mldsa87" "ML-DSA-87" Proof.MlDsa.X86.Scrub.inst87.params
    spSafe := Proof.MlDsa.X86.Scrub.prepareSecret_spSafe _ },
  Spec.MlDsa.sign44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.sign Spec.MlDsa.mlDsa44 "mldsa44"
    verified := Proof.MlDsa.X86.Scrub.sign_scrubbed Proof.MlDsa.X86.Scrub.inst44 "ML-DSA-44"
    spSafe := Proof.MlDsa.X86.Scrub.sign_spSafe Proof.MlDsa.X86.Scrub.inst44 },
  Spec.MlDsa.sign65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.sign Spec.MlDsa.mlDsa65 "mldsa65"
    verified := Proof.MlDsa.X86.Scrub.sign_scrubbed Proof.MlDsa.X86.Scrub.inst65 "ML-DSA-65"
    spSafe := Proof.MlDsa.X86.Scrub.sign_spSafe Proof.MlDsa.X86.Scrub.inst65 },
  Spec.MlDsa.sign87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.sign Spec.MlDsa.mlDsa87 "mldsa87"
    verified := Proof.MlDsa.X86.Scrub.sign_scrubbed Proof.MlDsa.X86.Scrub.inst87 "ML-DSA-87"
    spSafe := Proof.MlDsa.X86.Scrub.sign_spSafe Proof.MlDsa.X86.Scrub.inst87 },
  Spec.MlDsa.preparedSign44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signPrepared Spec.MlDsa.mlDsa44 "mldsa44"
    verified := Proof.MlDsa.X86.Scrub.signPrepared_scrubbed Proof.MlDsa.X86.Scrub.inst44 "ML-DSA-44"
    spSafe := Proof.MlDsa.X86.Scrub.signPrepared_spSafe Proof.MlDsa.X86.Scrub.inst44 },
  Spec.MlDsa.preparedSign65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signPrepared Spec.MlDsa.mlDsa65 "mldsa65"
    verified := Proof.MlDsa.X86.Scrub.signPrepared_scrubbed Proof.MlDsa.X86.Scrub.inst65 "ML-DSA-65"
    spSafe := Proof.MlDsa.X86.Scrub.signPrepared_spSafe Proof.MlDsa.X86.Scrub.inst65 },
  Spec.MlDsa.preparedSign87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signPrepared Spec.MlDsa.mlDsa87 "mldsa87"
    verified := Proof.MlDsa.X86.Scrub.signPrepared_scrubbed Proof.MlDsa.X86.Scrub.inst87 "ML-DSA-87"
    spSafe := Proof.MlDsa.X86.Scrub.signPrepared_spSafe Proof.MlDsa.X86.Scrub.inst87 },
  Spec.MlDsa.signMessage44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signMessage Spec.MlDsa.mlDsa44 "mldsa44"
    verified := Proof.MlDsa.X86.Scrub.signMessage_scrubbed Proof.MlDsa.X86.Scrub.inst44 "ML-DSA-44"
    spSafe := Proof.MlDsa.X86.Scrub.signMessage_spSafe Proof.MlDsa.X86.Scrub.inst44 },
  Spec.MlDsa.preparedSignMessage44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedSignMessage Spec.MlDsa.mlDsa44 "mldsa44"
    verified := Proof.MlDsa.X86.Scrub.preparedSignMessage_scrubbed Proof.MlDsa.X86.Scrub.inst44 "ML-DSA-44"
    spSafe := Proof.MlDsa.X86.Scrub.preparedSignMessage_spSafe Proof.MlDsa.X86.Scrub.inst44 },
  Spec.MlDsa.signMessage65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signMessage Spec.MlDsa.mlDsa65 "mldsa65"
    verified := Proof.MlDsa.X86.Scrub.signMessage_scrubbed Proof.MlDsa.X86.Scrub.inst65 "ML-DSA-65"
    spSafe := Proof.MlDsa.X86.Scrub.signMessage_spSafe Proof.MlDsa.X86.Scrub.inst65 },
  Spec.MlDsa.preparedSignMessage65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedSignMessage Spec.MlDsa.mlDsa65 "mldsa65"
    verified := Proof.MlDsa.X86.Scrub.preparedSignMessage_scrubbed Proof.MlDsa.X86.Scrub.inst65 "ML-DSA-65"
    spSafe := Proof.MlDsa.X86.Scrub.preparedSignMessage_spSafe Proof.MlDsa.X86.Scrub.inst65 },
  Spec.MlDsa.signMessage87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signMessage Spec.MlDsa.mlDsa87 "mldsa87"
    verified := Proof.MlDsa.X86.Scrub.signMessage_scrubbed Proof.MlDsa.X86.Scrub.inst87 "ML-DSA-87"
    spSafe := Proof.MlDsa.X86.Scrub.signMessage_spSafe Proof.MlDsa.X86.Scrub.inst87 },
  Spec.MlDsa.preparedSignMessage87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedSignMessage Spec.MlDsa.mlDsa87 "mldsa87"
    verified := Proof.MlDsa.X86.Scrub.preparedSignMessage_scrubbed Proof.MlDsa.X86.Scrub.inst87 "ML-DSA-87"
    spSafe := Proof.MlDsa.X86.Scrub.preparedSignMessage_spSafe Proof.MlDsa.X86.Scrub.inst87 },
  Spec.MlDsa.verify44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verify Spec.MlDsa.mlDsa44 "mldsa44"
    verified := Proof.MlDsa.X86.Scrub.verify_scrubbed Proof.MlDsa.X86.Scrub.inst44 "ML-DSA-44"
    spSafe := Proof.MlDsa.X86.Scrub.verify_spSafe Proof.MlDsa.X86.Scrub.inst44 },
  Spec.MlDsa.verify65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verify Spec.MlDsa.mlDsa65 "mldsa65"
    verified := Proof.MlDsa.X86.Scrub.verify_scrubbed Proof.MlDsa.X86.Scrub.inst65 "ML-DSA-65"
    spSafe := Proof.MlDsa.X86.Scrub.verify_spSafe Proof.MlDsa.X86.Scrub.inst65 },
  Spec.MlDsa.verify87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verify Spec.MlDsa.mlDsa87 "mldsa87"
    verified := Proof.MlDsa.X86.Scrub.verify_scrubbed Proof.MlDsa.X86.Scrub.inst87 "ML-DSA-87"
    spSafe := Proof.MlDsa.X86.Scrub.verify_spSafe Proof.MlDsa.X86.Scrub.inst87 },
  Spec.MlDsa.preparedVerify44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyPrepared Spec.MlDsa.mlDsa44 "mldsa44"
    verified := Proof.MlDsa.X86.Scrub.verifyPrepared_scrubbed Proof.MlDsa.X86.Scrub.inst44 "ML-DSA-44"
    spSafe := Proof.MlDsa.X86.Scrub.verifyPrepared_spSafe Proof.MlDsa.X86.Scrub.inst44 },
  Spec.MlDsa.preparedVerify65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyPrepared Spec.MlDsa.mlDsa65 "mldsa65"
    verified := Proof.MlDsa.X86.Scrub.verifyPrepared_scrubbed Proof.MlDsa.X86.Scrub.inst65 "ML-DSA-65"
    spSafe := Proof.MlDsa.X86.Scrub.verifyPrepared_spSafe Proof.MlDsa.X86.Scrub.inst65 },
  Spec.MlDsa.preparedVerify87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyPrepared Spec.MlDsa.mlDsa87 "mldsa87"
    verified := Proof.MlDsa.X86.Scrub.verifyPrepared_scrubbed Proof.MlDsa.X86.Scrub.inst87 "ML-DSA-87"
    spSafe := Proof.MlDsa.X86.Scrub.verifyPrepared_spSafe Proof.MlDsa.X86.Scrub.inst87 },
  Spec.MlDsa.verifyMessageCached44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyMessageCached Spec.MlDsa.mlDsa44 "mldsa44"
    verified := Proof.MlDsa.X86.Scrub.verifyMessageCached_scrubbed Proof.MlDsa.X86.Scrub.inst44 "ML-DSA-44"
    spSafe := Proof.MlDsa.X86.Scrub.verifyMessageCached_spSafe Proof.MlDsa.X86.Scrub.inst44 },
  Spec.MlDsa.preparedVerifyMessage44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa44 "mldsa44"
    verified := Proof.MlDsa.X86.Scrub.preparedVerifyMessage_scrubbed Proof.MlDsa.X86.Scrub.inst44 "ML-DSA-44"
    spSafe := Proof.MlDsa.X86.Scrub.preparedVerifyMessage_spSafe Proof.MlDsa.X86.Scrub.inst44 },
  Spec.MlDsa.verifyMessageCached65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyMessageCached Spec.MlDsa.mlDsa65 "mldsa65"
    verified := Proof.MlDsa.X86.Scrub.verifyMessageCached_scrubbed Proof.MlDsa.X86.Scrub.inst65 "ML-DSA-65"
    spSafe := Proof.MlDsa.X86.Scrub.verifyMessageCached_spSafe Proof.MlDsa.X86.Scrub.inst65 },
  Spec.MlDsa.preparedVerifyMessage65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa65 "mldsa65"
    verified := Proof.MlDsa.X86.Scrub.preparedVerifyMessage_scrubbed Proof.MlDsa.X86.Scrub.inst65 "ML-DSA-65"
    spSafe := Proof.MlDsa.X86.Scrub.preparedVerifyMessage_spSafe Proof.MlDsa.X86.Scrub.inst65 },
  Spec.MlDsa.verifyMessageCached87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyMessageCached Spec.MlDsa.mlDsa87 "mldsa87"
    verified := Proof.MlDsa.X86.Scrub.verifyMessageCached_scrubbed Proof.MlDsa.X86.Scrub.inst87 "ML-DSA-87"
    spSafe := Proof.MlDsa.X86.Scrub.verifyMessageCached_spSafe Proof.MlDsa.X86.Scrub.inst87 },
  Spec.MlDsa.preparedVerifyMessage87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa87 "mldsa87"
    verified := Proof.MlDsa.X86.Scrub.preparedVerifyMessage_scrubbed Proof.MlDsa.X86.Scrub.inst87 "ML-DSA-87"
    spSafe := Proof.MlDsa.X86.Scrub.preparedVerifyMessage_spSafe Proof.MlDsa.X86.Scrub.inst87 }]

spec_apis artifacts

end VG.Artifacts.MlDsa.X86
