module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Scrub
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.PkTr
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Inst

/-! # ML-DSA (FIPS 204) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsa.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.keyGen44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.keyGen44_scrubbed },
  Spec.MlDsa.keyGen65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.keyGen65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.keyGen65_scrubbed },
  Spec.MlDsa.keyGen87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.keyGen87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.keyGen87_scrubbed },
  Spec.MlDsa.pkTr44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.pkTr44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.pkTr44_scrubbed },
  Spec.MlDsa.pkTr65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.pkTr65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.pkTr65_scrubbed },
  Spec.MlDsa.pkTr87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.pkTr87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.pkTr87_scrubbed },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.preparePublic44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.preparePublic44_scrubbed },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.prepareSecret44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.prepareSecret44_scrubbed },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.preparePublic65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.preparePublic65_scrubbed },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.prepareSecret65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.prepareSecret65_scrubbed },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.preparePublic87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.preparePublic87_scrubbed },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.prepareSecret87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.prepareSecret87_scrubbed },
  Spec.MlDsa.sign44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.sign44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.sign44_scrubbed },
  Spec.MlDsa.sign65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.sign65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.sign65_scrubbed },
  Spec.MlDsa.sign87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.sign87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.sign87_scrubbed },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.signPrepared44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.signPrepared44_scrubbed },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.signPrepared65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.signPrepared65_scrubbed },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.signPrepared87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.signPrepared87_scrubbed },
  Spec.MlDsa.signMessage44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.signMessage44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.signMessage44_scrubbed },
  Spec.MlDsa.signMessage65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.signMessage65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.signMessage65_scrubbed },
  Spec.MlDsa.signMessage87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.signMessage87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.signMessage87_scrubbed },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.preparedSignMessage44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.preparedSignMessage44_scrubbed },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.preparedSignMessage65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.preparedSignMessage65_scrubbed },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.preparedSignMessage87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.preparedSignMessage87_scrubbed },
  Spec.MlDsa.verify44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.verify44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.verify44_scrubbed },
  Spec.MlDsa.verify65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.verify65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.verify65_scrubbed },
  Spec.MlDsa.verify87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.verify87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.verify87_scrubbed },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.verifyPrepared44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.verifyPrepared44_scrubbed },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.verifyPrepared65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.verifyPrepared65_scrubbed },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.verifyPrepared87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.verifyPrepared87_scrubbed },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.verifyMessageCached44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.verifyMessageCached44_scrubbed },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.verifyMessageCached65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.verifyMessageCached65_scrubbed },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.verifyMessageCached87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.verifyMessageCached87_scrubbed },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.preparedVerifyMessage44
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.preparedVerifyMessage44_scrubbed },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.preparedVerifyMessage65
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.preparedVerifyMessage65_scrubbed },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Fn.preparedVerifyMessage87
    verified := .scrubbed Proof.MlDsa.PPC64LE.Scrub.preparedVerifyMessage87_scrubbed }]

end VG.Artifacts.MlDsa.PPC64LE
