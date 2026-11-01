module

public import VerifiedGarbage.Proof.AesXts.RISCV64.Verified
public import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesXts.RISCV64.Lit

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesXts.RISCV64

open VG.Proof.AesXts.RISCV64

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact RISCV64.target {
    code := Impl.AesXts.RISCV64Unit.encrypt
    verified := Unit.encrypt_verified },
  Spec.Xts.aesDecryptUnitApi.artifact RISCV64.target {
    code := Impl.AesXts.RISCV64Unit.decrypt
    verified := Unit.decrypt_verified }]

end VG.Artifacts.AesXts.RISCV64
