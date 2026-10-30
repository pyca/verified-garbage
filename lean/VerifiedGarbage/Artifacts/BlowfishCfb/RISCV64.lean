module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit

/-! # Blowfish-CFB64 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.cfbEncrypt
    stack := 4224
    verified := Proof.Blowfish.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Blowfish.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.cfbDecrypt
    stack := 4224
    verified := Proof.Blowfish.RISCV64.Modes.cfbDecrypt_verified }]

end VG.Artifacts.BlowfishCfb.RISCV64
