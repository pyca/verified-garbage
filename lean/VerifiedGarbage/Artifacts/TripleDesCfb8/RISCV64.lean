module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-! # Triple DES-CFB8 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.cfb8Encrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cfb8Encrypt_verified },
  Spec.TripleDes.cfb8DecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.cfb8Decrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cfb8Decrypt_verified }]

end VG.Artifacts.TripleDesCfb8.RISCV64
