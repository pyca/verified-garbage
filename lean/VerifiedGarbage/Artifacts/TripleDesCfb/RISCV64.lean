module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-! # Triple DES-CFB64 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.cfbEncrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cfbEncrypt_verified },
  Spec.TripleDes.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.cfbDecrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cfbDecrypt_verified }]

end VG.Artifacts.TripleDesCfb.RISCV64
