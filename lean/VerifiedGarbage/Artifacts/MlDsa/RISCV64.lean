module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ML-DSA (FIPS 204) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlDsa.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.keyGen44Reg,
  Spec.MlDsa.keyGen65Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.keyGen65Reg,
  Spec.MlDsa.keyGen87Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.keyGen87Reg,
  Spec.MlDsa.pkTr44Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.pkTr44Reg,
  Spec.MlDsa.pkTr65Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.pkTr65Reg,
  Spec.MlDsa.pkTr87Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.pkTr87Reg,
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.preparePublic44Reg,
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.prepareSecret44Reg,
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.preparePublic65Reg,
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.prepareSecret65Reg,
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.preparePublic87Reg,
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.prepareSecret87Reg,
  Spec.MlDsa.sign44Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.sign44Reg,
  Spec.MlDsa.sign65Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.sign65Reg,
  Spec.MlDsa.sign87Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.sign87Reg,
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.signPrepared44Reg,
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.signPrepared65Reg,
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.signPrepared87Reg,
  Spec.MlDsa.signMessage44Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.signMessage44Reg,
  Spec.MlDsa.signMessage65Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.signMessage65Reg,
  Spec.MlDsa.signMessage87Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.signMessage87Reg,
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target
    Proof.MlDsa.RISCV64.Scrub.preparedSignMessage44Reg,
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target
    Proof.MlDsa.RISCV64.Scrub.preparedSignMessage65Reg,
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target
    Proof.MlDsa.RISCV64.Scrub.preparedSignMessage87Reg,
  Spec.MlDsa.verify44Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.verify44Reg,
  Spec.MlDsa.verify65Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.verify65Reg,
  Spec.MlDsa.verify87Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.verify87Reg,
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.verifyPrepared44Reg,
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.verifyPrepared65Reg,
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.verifyPrepared87Reg,
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target
    Proof.MlDsa.RISCV64.Scrub.verifyMessageCached44Reg,
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target
    Proof.MlDsa.RISCV64.Scrub.verifyMessageCached65Reg,
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target
    Proof.MlDsa.RISCV64.Scrub.verifyMessageCached87Reg,
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target
    Proof.MlDsa.RISCV64.Scrub.preparedVerifyMessage44Reg,
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target
    Proof.MlDsa.RISCV64.Scrub.preparedVerifyMessage65Reg,
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target
    Proof.MlDsa.RISCV64.Scrub.preparedVerifyMessage87Reg]

end VG.Artifacts.MlDsa.RISCV64
