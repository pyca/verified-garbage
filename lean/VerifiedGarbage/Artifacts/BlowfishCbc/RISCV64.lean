module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit

/-! # Blowfish-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.cbcEncryptChained
    stack := 4224
    verified := Proof.Blowfish.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Blowfish.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.cbcDecryptChained
    stack := 4224
    verified := Proof.Blowfish.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.BlowfishCbc.RISCV64
