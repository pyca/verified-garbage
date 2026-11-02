module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreVerified
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubVerified
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtVerified
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivVerified
public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValVerified
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCkV
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCckV
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rsa.RISCV64

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact RISCV64.target {
    code := Impl.Bignum.RISCV64.Precompute.precompute
    verified := Proof.Bignum.RISCV64.Pre.precompute_verified },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact RISCV64.target {
    code := Impl.Bignum.RISCV64.PublicChecked.publicChecked
    verified := Proof.Bignum.RISCV64.Pub.publicChecked_verified },
  Spec.Rsa.privateCheckedApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Priv.code
    stack := Impl.Rsa.RISCV64.Priv.frameBytes
    verified := Proof.Rsa.RISCV64.Priv.priv_verified },
  Spec.Rsa.crtValuesApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.CrtValues.code
    verified := Proof.Rsa.RISCV64.CrtValues.crtValues_verified },
  Spec.Rsa.checkKeyApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.CheckKey.code
    verified := Proof.Rsa.RISCV64.KeyCheck.ck_verified },
  Spec.Rsa.checkCrtKeyApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.CheckCrtKey.code
    verified := Proof.Rsa.RISCV64.KeyCheck.cck_verified }]

end VG.Artifacts.Rsa.RISCV64
