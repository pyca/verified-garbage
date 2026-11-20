module

public import VerifiedGarbage.Proof.MlDsa.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # ML-DSA (FIPS 204) on x86 -/

@[expose] public section

namespace VG.Artifacts.MlDsa.X86

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.keyGen Spec.MlDsa.mlDsa44
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.keyGen_scrubbed "mldsa44" "ML-DSA-44" (.inl rfl))
    spSafe := Proof.MlDsa.X86.Scrub.keyGen_spSafe _ },
  Spec.MlDsa.keyGen65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.keyGen Spec.MlDsa.mlDsa65
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.keyGen_scrubbed "mldsa65" "ML-DSA-65" (.inr (.inl rfl)))
    spSafe := Proof.MlDsa.X86.Scrub.keyGen_spSafe _ },
  Spec.MlDsa.keyGen87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.keyGen Spec.MlDsa.mlDsa87
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.keyGen_scrubbed "mldsa87" "ML-DSA-87" (.inr (.inr rfl)))
    spSafe := Proof.MlDsa.X86.Scrub.keyGen_spSafe _ },
  Spec.MlDsa.pkTr44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.pkTr Spec.MlDsa.mlDsa44
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.pkTr_scrubbed "mldsa44" "ML-DSA-44" (.inl rfl))
    spSafe := Proof.MlDsa.X86.Scrub.pkTr_spSafe _ },
  Spec.MlDsa.pkTr65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.pkTr Spec.MlDsa.mlDsa65
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.pkTr_scrubbed "mldsa65" "ML-DSA-65" (.inr (.inl rfl)))
    spSafe := Proof.MlDsa.X86.Scrub.pkTr_spSafe _ },
  Spec.MlDsa.pkTr87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.pkTr Spec.MlDsa.mlDsa87
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.pkTr_scrubbed "mldsa87" "ML-DSA-87" (.inr (.inr rfl)))
    spSafe := Proof.MlDsa.X86.Scrub.pkTr_spSafe _ },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparePublic Spec.MlDsa.mlDsa44
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.preparePublic_scrubbed "mldsa44" "ML-DSA-44" (.inl rfl))
    spSafe := Proof.MlDsa.X86.Scrub.preparePublic_spSafe _ },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.prepareSecret Spec.MlDsa.mlDsa44
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.prepareSecret_scrubbed "mldsa44" "ML-DSA-44" (.inl rfl))
    spSafe := Proof.MlDsa.X86.Scrub.prepareSecret_spSafe _ },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparePublic Spec.MlDsa.mlDsa65
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.preparePublic_scrubbed "mldsa65" "ML-DSA-65" (.inr (.inl rfl)))
    spSafe := Proof.MlDsa.X86.Scrub.preparePublic_spSafe _ },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.prepareSecret Spec.MlDsa.mlDsa65
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.prepareSecret_scrubbed "mldsa65" "ML-DSA-65" (.inr (.inl rfl)))
    spSafe := Proof.MlDsa.X86.Scrub.prepareSecret_spSafe _ },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparePublic Spec.MlDsa.mlDsa87
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.preparePublic_scrubbed "mldsa87" "ML-DSA-87" (.inr (.inr rfl)))
    spSafe := Proof.MlDsa.X86.Scrub.preparePublic_spSafe _ },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.prepareSecret Spec.MlDsa.mlDsa87
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.prepareSecret_scrubbed "mldsa87" "ML-DSA-87" (.inr (.inr rfl)))
    spSafe := Proof.MlDsa.X86.Scrub.prepareSecret_spSafe _ },
  Spec.MlDsa.sign44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.sign Spec.MlDsa.mlDsa44 "mldsa44"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.sign_scrubbed (.inl ⟨rfl, rfl⟩) "ML-DSA-44")
    spSafe := Proof.MlDsa.X86.Scrub.sign_spSafe (.inl ⟨rfl, rfl⟩) },
  Spec.MlDsa.sign65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.sign Spec.MlDsa.mlDsa65 "mldsa65"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.sign_scrubbed (.inr (.inl ⟨rfl, rfl⟩)) "ML-DSA-65")
    spSafe := Proof.MlDsa.X86.Scrub.sign_spSafe (.inr (.inl ⟨rfl, rfl⟩)) },
  Spec.MlDsa.sign87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.sign Spec.MlDsa.mlDsa87 "mldsa87"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.sign_scrubbed (.inr (.inr ⟨rfl, rfl⟩)) "ML-DSA-87")
    spSafe := Proof.MlDsa.X86.Scrub.sign_spSafe (.inr (.inr ⟨rfl, rfl⟩)) },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signPrepared Spec.MlDsa.mlDsa44 "mldsa44"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.signPrepared_scrubbed (.inl ⟨rfl, rfl⟩) "ML-DSA-44")
    spSafe := Proof.MlDsa.X86.Scrub.signPrepared_spSafe (.inl ⟨rfl, rfl⟩) },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signPrepared Spec.MlDsa.mlDsa65 "mldsa65"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.signPrepared_scrubbed (.inr (.inl ⟨rfl, rfl⟩)) "ML-DSA-65")
    spSafe := Proof.MlDsa.X86.Scrub.signPrepared_spSafe (.inr (.inl ⟨rfl, rfl⟩)) },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signPrepared Spec.MlDsa.mlDsa87 "mldsa87"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.signPrepared_scrubbed (.inr (.inr ⟨rfl, rfl⟩)) "ML-DSA-87")
    spSafe := Proof.MlDsa.X86.Scrub.signPrepared_spSafe (.inr (.inr ⟨rfl, rfl⟩)) },
  Spec.MlDsa.signMessage44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signMessage Spec.MlDsa.mlDsa44 "mldsa44"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.signMessage_scrubbed (.inl ⟨rfl, rfl⟩) "ML-DSA-44")
    spSafe := Proof.MlDsa.X86.Scrub.signMessage_spSafe (.inl ⟨rfl, rfl⟩) },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedSignMessage Spec.MlDsa.mlDsa44 "mldsa44"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.preparedSignMessage_scrubbed (.inl ⟨rfl, rfl⟩) "ML-DSA-44")
    spSafe := Proof.MlDsa.X86.Scrub.preparedSignMessage_spSafe (.inl ⟨rfl, rfl⟩) },
  Spec.MlDsa.signMessage65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signMessage Spec.MlDsa.mlDsa65 "mldsa65"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.signMessage_scrubbed (.inr (.inl ⟨rfl, rfl⟩)) "ML-DSA-65")
    spSafe := Proof.MlDsa.X86.Scrub.signMessage_spSafe (.inr (.inl ⟨rfl, rfl⟩)) },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedSignMessage Spec.MlDsa.mlDsa65 "mldsa65"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.preparedSignMessage_scrubbed (.inr (.inl ⟨rfl, rfl⟩)) "ML-DSA-65")
    spSafe := Proof.MlDsa.X86.Scrub.preparedSignMessage_spSafe (.inr (.inl ⟨rfl, rfl⟩)) },
  Spec.MlDsa.signMessage87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.signMessage Spec.MlDsa.mlDsa87 "mldsa87"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.signMessage_scrubbed (.inr (.inr ⟨rfl, rfl⟩)) "ML-DSA-87")
    spSafe := Proof.MlDsa.X86.Scrub.signMessage_spSafe (.inr (.inr ⟨rfl, rfl⟩)) },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedSignMessage Spec.MlDsa.mlDsa87 "mldsa87"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.preparedSignMessage_scrubbed (.inr (.inr ⟨rfl, rfl⟩)) "ML-DSA-87")
    spSafe := Proof.MlDsa.X86.Scrub.preparedSignMessage_spSafe (.inr (.inr ⟨rfl, rfl⟩)) },
  Spec.MlDsa.verify44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verify Spec.MlDsa.mlDsa44 "mldsa44"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.verify_scrubbed (.inl ⟨rfl, rfl⟩) "ML-DSA-44")
    spSafe := Proof.MlDsa.X86.Scrub.verify_spSafe (.inl ⟨rfl, rfl⟩) },
  Spec.MlDsa.verify65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verify Spec.MlDsa.mlDsa65 "mldsa65"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.verify_scrubbed (.inr (.inl ⟨rfl, rfl⟩)) "ML-DSA-65")
    spSafe := Proof.MlDsa.X86.Scrub.verify_spSafe (.inr (.inl ⟨rfl, rfl⟩)) },
  Spec.MlDsa.verify87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verify Spec.MlDsa.mlDsa87 "mldsa87"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.verify_scrubbed (.inr (.inr ⟨rfl, rfl⟩)) "ML-DSA-87")
    spSafe := Proof.MlDsa.X86.Scrub.verify_spSafe (.inr (.inr ⟨rfl, rfl⟩)) },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyPrepared Spec.MlDsa.mlDsa44 "mldsa44"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.verifyPrepared_scrubbed (.inl ⟨rfl, rfl⟩) "ML-DSA-44")
    spSafe := Proof.MlDsa.X86.Scrub.verifyPrepared_spSafe (.inl ⟨rfl, rfl⟩) },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyPrepared Spec.MlDsa.mlDsa65 "mldsa65"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.verifyPrepared_scrubbed (.inr (.inl ⟨rfl, rfl⟩)) "ML-DSA-65")
    spSafe := Proof.MlDsa.X86.Scrub.verifyPrepared_spSafe (.inr (.inl ⟨rfl, rfl⟩)) },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyPrepared Spec.MlDsa.mlDsa87 "mldsa87"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.verifyPrepared_scrubbed (.inr (.inr ⟨rfl, rfl⟩)) "ML-DSA-87")
    spSafe := Proof.MlDsa.X86.Scrub.verifyPrepared_spSafe (.inr (.inr ⟨rfl, rfl⟩)) },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyMessageCached Spec.MlDsa.mlDsa44 "mldsa44"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.verifyMessageCached_scrubbed (.inl ⟨rfl, rfl⟩) "ML-DSA-44")
    spSafe := Proof.MlDsa.X86.Scrub.verifyMessageCached_spSafe (.inl ⟨rfl, rfl⟩) },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa44 "mldsa44"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.preparedVerifyMessage_scrubbed (.inl ⟨rfl, rfl⟩) "ML-DSA-44")
    spSafe := Proof.MlDsa.X86.Scrub.preparedVerifyMessage_spSafe (.inl ⟨rfl, rfl⟩) },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyMessageCached Spec.MlDsa.mlDsa65 "mldsa65"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.verifyMessageCached_scrubbed (.inr (.inl ⟨rfl, rfl⟩)) "ML-DSA-65")
    spSafe := Proof.MlDsa.X86.Scrub.verifyMessageCached_spSafe (.inr (.inl ⟨rfl, rfl⟩)) },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa65 "mldsa65"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.preparedVerifyMessage_scrubbed (.inr (.inl ⟨rfl, rfl⟩)) "ML-DSA-65")
    spSafe := Proof.MlDsa.X86.Scrub.preparedVerifyMessage_spSafe (.inr (.inl ⟨rfl, rfl⟩)) },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.verifyMessageCached Spec.MlDsa.mlDsa87 "mldsa87"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.verifyMessageCached_scrubbed (.inr (.inr ⟨rfl, rfl⟩)) "ML-DSA-87")
    spSafe := Proof.MlDsa.X86.Scrub.verifyMessageCached_spSafe (.inr (.inr ⟨rfl, rfl⟩)) },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa87 "mldsa87"
    verified := .scrubbed (Proof.MlDsa.X86.Scrub.preparedVerifyMessage_scrubbed (.inr (.inr ⟨rfl, rfl⟩)) "ML-DSA-87")
    spSafe := Proof.MlDsa.X86.Scrub.preparedVerifyMessage_spSafe (.inr (.inr ⟨rfl, rfl⟩)) }]

end VG.Artifacts.MlDsa.X86
