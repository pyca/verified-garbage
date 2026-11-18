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
  Spec.MlDsa.keyGen44Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.keyGen44Reg,
  Spec.MlDsa.keyGen65Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.keyGen65Reg,
  Spec.MlDsa.keyGen87Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.keyGen87Reg,
  Spec.MlDsa.pkTr44Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.pkTr44Reg,
  Spec.MlDsa.pkTr65Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.pkTr65Reg,
  Spec.MlDsa.pkTr87Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.pkTr87Reg,
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.preparePublic44Reg,
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.prepareSecret44Reg,
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.preparePublic65Reg,
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.prepareSecret65Reg,
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.preparePublic87Reg,
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.prepareSecret87Reg,
  Spec.MlDsa.sign44Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.sign44Reg,
  Spec.MlDsa.sign65Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.sign65Reg,
  Spec.MlDsa.sign87Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.sign87Reg,
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.signPrepared44Reg,
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.signPrepared65Reg,
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.signPrepared87Reg,
  Spec.MlDsa.signMessage44Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.signMessage44Reg,
  Spec.MlDsa.signMessage65Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.signMessage65Reg,
  Spec.MlDsa.signMessage87Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.signMessage87Reg,
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.preparedSignMessage44Reg,
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.preparedSignMessage65Reg,
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.preparedSignMessage87Reg,
  Spec.MlDsa.verify44Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.verify44Reg,
  Spec.MlDsa.verify65Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.verify65Reg,
  Spec.MlDsa.verify87Api.artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.verify87Reg,
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.verifyPrepared44Reg,
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.verifyPrepared65Reg,
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.verifyPrepared87Reg,
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.verifyMessageCached44Reg,
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.verifyMessageCached65Reg,
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.verifyMessageCached87Reg,
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.preparedVerifyMessage44Reg,
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.preparedVerifyMessage65Reg,
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target Proof.MlDsa.PPC64LE.Scrub.preparedVerifyMessage87Reg]

end VG.Artifacts.MlDsa.PPC64LE
